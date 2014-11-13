module Test.Info2.Cyp (
  proof
, proofFile
) where

import Control.Monad
import Control.Monad.State
import Data.Foldable (for_)
import Data.List
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Traversable (traverse)
import qualified Text.Parsec as Parsec
import Text.PrettyPrint (colon, comma, fsep, punctuate, quotes, text, vcat, (<>), (<+>), ($+$))

import Test.Info2.Cyp.Env
import Test.Info2.Cyp.Parser
import Test.Info2.Cyp.Term
import Test.Info2.Cyp.Types
import Test.Info2.Cyp.Util

proofFile :: FilePath -> FilePath -> IO (Err ())
proofFile masterFile studentFile = do
    mContent <- readFile masterFile
    sContent <- readFile studentFile
    return $ proof (masterFile, mContent) (studentFile, sContent)

proof :: (String, String) -> (String, String) -> Err ()
proof (mName, mContent) (sName, sContent) = do
    env <- processMasterFile mName mContent
    lemmaStmts <- processProofFile env sName sContent
    results <- checkProofs env lemmaStmts
    case filter (not . contained results) $ goals env of
        [] -> return ()
        xs -> err $ indent (text "The following goals are still open:") $
            vcat $ map unparseProp xs
  where
    contained props goal = any (\x -> isJust $ matchProp goal (namedVal x) []) props

processMasterFile :: FilePath -> String -> Err Env
processMasterFile path content = errCtxtStr "Parsing background theory" $ do
    mResult <- eitherToErr $ Parsec.parse cthyParser path content
    dts <- readDataType mResult
    syms <- fmap (defaultConsts ++) $ readSym mResult
    (fundefs, consts) <- readFunc syms mResult
    axs <- readAxiom consts mResult
    gls <- readGoal consts mResult
    return $ Env { datatypes = dts, axioms = fundefs ++ axs,
        constants = nub $ consts, fixes = M.empty, goals = gls }

processProofFile :: Env -> FilePath -> String -> Err [ParseLemma]
processProofFile env path content = errCtxtStr "Parsing proof" $
    eitherToErr $ Parsec.runParser cprfParser env path content

checkProofs :: Env -> [ParseLemma] -> Err [Named Prop]
checkProofs env []  = Right $ axioms env
checkProofs env (l : ls) = do
    (_, env') <- checkLemma l env
    checkProofs env' ls

checkLemma :: ParseLemma -> Env -> Err (Prop, Env)
checkLemma (ParseLemma name rprop proof) env = errCtxt (text "Lemma" <+> text name <> colon <+> unparseRawProp rprop) $ do
    let (prop, env') = declareProp rprop env
    Prop _ _ <- checkProof prop proof env'
    let proved = generalizeEnvProp env prop
    return (proved, env { axioms = Named name proved : axioms env })

checkProof :: Prop -> ParseProof -> Env -> Err Prop
checkProof _ ParseCheating _ = err $ text "Cheating detected"
checkProof prop (ParseEquation reqns) env = errCtxtStr "Equational proof" $ do
    let (eqns, env') = runState (traverse (state . declareTerm) reqns) env
    proved <- validEqnSeqq (axioms env') eqns
    when (prop /= proved) $ err $
        text "Proved proposition does not match goal:" `indent` unparseProp proved
    return proved
checkProof prop (ParseExt withRaw toShowRaw proof) env = errCtxt ctxtMsg $
    flip evalStateT env $ do
        with <- validateWith withRaw
        prop' <- validateShow with toShowRaw
        env <- get
        lift $ checkProof prop' proof env
  where
    ctxtMsg = text "Extensionality with" <+> quotes (unparseRawTerm withRaw)

    validateWith t = do -- lazy code duplication
        t' <- state (declareTerm t)
        case t' of
            Free v -> return v
            _ -> lift $ err $ text "Term" <+> quotes (unparseTerm t')
                <+> text "is not a valid variable for extensionality"

    validateShow v raw = do
        prop' <- state (declareProp raw)
        let Prop lhs rhs = prop
        let Prop lhs' rhs' = prop'
        let lhsE = Application lhs (Free v)
        let rhsE = Application rhs (Free v)
        when (lhsE /= lhs') $ bail "Invalid left-hand side of proposition, expected:" lhsE
        when (rhsE /= rhs') $ bail "Invalid right-hand side of proposition, expected:" rhsE
        return prop'
      where
        bail msg t = lift $ err $ text msg <+> quotes (unparseTerm t)
checkProof prop (ParseInduction dtRaw overRaw casesRaw) env = errCtxt ctxtMsg $ do
    flip evalStateT env $ do
        dt <- lift (validateDatatype dtRaw)
        over <- validateOver overRaw
        env <- get
        lift $ validateCases prop dt over casesRaw env
        return prop
  where
    ctxtMsg = text "Induction over variable"
        <+> quotes (unparseRawTerm overRaw) <+> text "of type" <+> quotes (text dtRaw)

    validateDatatype name = case find (\dt -> getDtName dt == name) (datatypes env) of
        Nothing -> err $ fsep $
            [ text "Invalid datatype" <+> quotes (text name) <> text "."
            , text "Expected one of:" ]
            ++ punctuate comma (map (quotes . text . getDtName) $ datatypes env)
        Just dt -> Right dt

    validateOver t = do
        t' <- state (declareTerm t)
        case t' of
            Free v -> return v
            _ -> lift $ err $ text "Term" <+> quotes (unparseTerm t')
                <+> text "is not a valid induction variable"

    validateCases prop dt over cases env = do
        caseNames <- traverse (validateCase prop dt over env) cases
        case missingCase caseNames of
            Nothing -> return ()
            Just (name, _) -> errStr $ "Missing case '" ++ name ++ "'"
      where
        missingCase caseNames = find (\(name, _) -> name `notElem` caseNames) (getDtConss dt)

    validateCase prop dt over env pc = errCtxt (text "Case" <+> quotes (unparseRawTerm $ pcCons pc)) $ do
        flip evalStateT env $ do
            caseT <- state (variantFixesTerm $ pcCons pc)
            (consName, consArgNs) <- lift $ lookupCons caseT dt
            let recArgNames = map snd . filter (\x -> fst x == TRec) $ consArgNs

            let subgoal = substFreeProp prop [(over, caseT)]

            case pcToShow pc of
                Nothing ->
                    lift $ err $ text "Missing 'To show'"
                Just raw -> do
                    toShow <- state (declareProp raw)
                    when (subgoal /= toShow) $ lift . err
                         $ text "'To show' does not match subgoal:"
                         `indent` (
                            text "To show:" <+> unparseProp toShow
                            $+$ debug (text "Subgoal:" <+> unparseProp subgoal))

                    userHyps <- checkPcHyps prop over recArgNames $ pcAssms pc

                    modify (\env -> env { axioms = userHyps ++ axioms env })
                    env <- get
                    Prop _ _ <- lift $ checkProof subgoal (pcProof pc) env
                    return consName

    lookupCons t (DataType _ conss) = errCtxt invCaseMsg $ do
        (consName, consArgs) <- findCons cons
        argNames <- traverse argName args
        when (not $ nub args == args) $
            errStr "Constructor arguments must be distinct"
        when (not $ length args == length consArgs) $
            errStr "Invalid number of arguments"
        return (consName, zip consArgs argNames)
      where
        (cons, args) = stripComb t

        argName (Free v) = return v
        argName _ = errStr "Constructor arguments must be variables"

        findCons (Const name) = case find (\c -> fst c == name) conss of
            Nothing -> err (text "Invalid constructor, expected one of"
                <+> (fsep . punctuate comma . map (quotes . text . fst) $ conss))
            Just x -> return x
        findCons _ = errStr "Outermost symbol is not a constant"

        invCaseMsg = text "Invalid case" <+> quotes (unparseTerm t) <> comma

    -- XXX rename
    checkPcHyps :: Prop -> IdxName -> [IdxName] -> [Named RawProp] -> StateT Env Err [Named Prop]
    checkPcHyps prop over recVars rpcHyps = do
        pcHyps <- traverse (traverse (state . declareProp)) rpcHyps
        let indHyps = map (substFreeProp prop . instOver) recVars
        lift $ for_ pcHyps $ \(Named name prop) -> case prop `elem` indHyps of
            True -> return ()
            False -> err $
                text ("Induction hypothesis " ++ name ++ " is not valid")
                `indent` (debug (unparseProp prop))
        return $ map (fmap $ generalizeExceptProp recVars) pcHyps
      where
        instOver n = [(over, Free n)]

    getDtConss (DataType _ conss) = conss
    getDtName (DataType n _) = n

validEqnSeq :: [Named Prop] -> EqnSeq Term -> Err Prop
validEqnSeq _ (Single t) = return (Prop t t)
validEqnSeq rules (Step t1 rule es)
    | rewritesToWith rule rules t1 t2 = do
        Prop _ tLast <- validEqnSeq rules es
        return (Prop t1 tLast)
    | otherwise = errCtxtStr ("Invalid proof step" ++ noRuleMsg) $ err $
        unparseTerm t1 $+$ text ("(by " ++ rule ++ ") " ++ symPropEq) <+> unparseTerm t2
        $+$ debug (text rule <> text ":" <+> vcat (map (unparseProp . namedVal) $ filter (\x -> namedName x == rule) rules))
  where
    (t2, _) = eqnSeqEnds es
    noRuleMsg
        | any (\x -> namedName x == rule) rules = ""
        | otherwise = " (no rules with name \"" ++ rule ++ "\")"

validEqnSeqq :: [Named Prop] -> EqnSeqq Term -> Err Prop
validEqnSeqq rules (EqnSeqq es1 Nothing) = validEqnSeq rules es1
validEqnSeqq rules (EqnSeqq es1 (Just es2)) = do
    Prop th1 tl1 <- validEqnSeq rules es1
    Prop th2 tl2 <- validEqnSeq rules es2
    case tl1 == tl2 of
        True -> return (Prop th1 th2)
        False -> errCtxtStr "Two equation chains don't fit together:" $
            err $ unparseTerm tl1 $+$ text symPropEq $+$ unparseTerm tl2

rewriteTop :: Term -> Prop -> Maybe Term
rewriteTop t (Prop lhs rhs) = fmap (subst rhs) $ match t lhs []

rewrite :: Term -> Prop -> [Term]
rewrite t@(Application f a) prop =
    maybeToList (rewriteTop t prop)
    ++ map (\x -> Application x a) (rewrite f prop)
    ++ map (Application f) (rewrite a prop)
rewrite t prop = maybeToList $ rewriteTop t prop

rewritesTo :: [Prop] -> Term -> Term -> Bool
rewritesTo rules l r = l == r || rewrites l r || rewrites r l
  where rewrites from to = any (\x -> isJust $ match to x []) $ concatMap (rewrite from) rules

rewritesToWith :: String -> [Named Prop] -> Term -> Term -> Bool
rewritesToWith name rules l r = rewritesTo (f rules) l r
  where f = map namedVal . filter (\x -> namedName x == name)
