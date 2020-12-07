{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

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
import qualified Text.Parsec as Parsec
import Text.PrettyPrint (colon, comma, fsep, hsep, int, punctuate, quotes, text, vcat, (<>), (<+>), ($+$))

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
    mResult <- eitherToErrWith showParsecErr $ Parsec.parse cthyParser path content
    dts <- readDataType mResult
    syms <- (defaultConsts ++) <$> readSym mResult
    (fundefs, consts) <- readFunc syms mResult
    axs <- readAxiom consts mResult
    gls <- readGoal consts mResult
    return $ Env { datatypes = dts, axioms = fundefs ++ axs,
        constants = nub consts, fixes = M.empty, goals = gls }

processProofFile :: Env -> FilePath -> String -> Err [ParseLemma]
processProofFile env path content = errCtxtStr "Parsing proof" $
    eitherToErrWith showParsecErr $ Parsec.runParser cprfParser env path content

checkProofs :: Env -> [ParseLemma] -> Err [Named Prop]
checkProofs env []  = Right $ axioms env
checkProofs env (l : ls) = do
    (_, env') <- checkLemma l env
    checkProofs env' ls

checkLemma :: ParseLemma -> Env -> Err (Prop, Env)
checkLemma (ParseLemma name rprop proof) env = errCtxt (text "Lemma" <+> text name Text.PrettyPrint.<> colon <+> unparseRawProp rprop) $ do
    let (prop, env') = declareProp rprop env
    Prop _ _ <- checkProof prop proof env'
    let proved = generalizeEnvProp env prop
    return (proved, env { axioms = Named name proved : axioms env })

checkProof :: Prop -> ParseProof -> Env -> Err Prop
checkProof _ ParseCheating _ = err $ text "Cheating detected"

checkProof prop (ParseEquation reqns) env = errCtxtStr "Equational proof" $ do
    let (eqns, env') = runState (traverse (state . declareTerm) reqns) env
    proved <- validEqnSeqq (axioms env') eqns
    when (prop /= proved && Prop (propRhs prop) (propLhs prop) /= proved) $ err $
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
    dt <- validDatatype dtRaw env
    flip evalStateT env $ do
        over <- validateOver overRaw
        env <- get
        lift $ validateCases dt over casesRaw env
        return prop
  where
    ctxtMsg = text "Induction over variable"
        <+> quotes (unparseRawTerm overRaw) <+> text "of type" <+> quotes (text dtRaw)

    validateOver t = do
        t' <- state (declareTerm t)
        case t' of
            Free v -> return v
            _ -> lift $ err $ text "Term" <+> quotes (unparseTerm t')
                <+> text "is not a valid induction variable"

    validateCases dt over cases env = do
        caseNames <- traverse (validateCase dt over env) cases
        case missingCase caseNames of
            Nothing -> return ()
            Just (name, _) -> errStr $ "Missing case '" ++ name ++ "'"
      where
        missingCase caseNames = find (\(name, _) -> name `notElem` caseNames) (dtConss dt)

    validateCase dt over env ParseCase{pcCons = pcc, pcBody = pcb} = errCtxt (text "Case" <+> quotes (unparseRawTerm pcc)) $ do
        flip evalStateT env $ do
            caseT <- state (variantFixesTerm pcc)
            (consName, consArgNs) <- lift $ validConsCase caseT dt
            let recArgNames = map snd $ filter (\x -> fst x == TRec) consArgNs

            let subgoal = substFreeProp prop [(over, caseT)]

            case pcbToShow pcb of
                Nothing ->
                    lift $ err $ text "Missing 'To show'"
                Just raw -> do
                    toShow <- state (declareProp raw)
                    when (subgoal /= toShow) $ lift . err
                         $ text "'To show' does not match subgoal:"
                         `indent` (
                            text "To show:" <+> unparseProp toShow
                            $+$ debug (text "Subgoal:" <+> unparseProp subgoal))

                    userHyps <- checkPcHyps over recArgNames $ pcbAssms pcb

                    modify (\env -> env { axioms = userHyps ++ axioms env })
                    env <- get
                    Prop _ _ <- lift $ checkProof subgoal (pcbProof pcb) env
                    return consName

    checkPcHyps over recVars rpcHyps = do
        pcHyps <- traverse (traverse (state . declareProp)) rpcHyps
        let indHyps = map (substFreeProp prop . instOver) recVars
        lift $ for_ pcHyps $ \(Named name prop) ->
            if prop `elem` indHyps then return ()
            else err $
                text ("Induction hypothesis " ++ name ++ " is not valid")
                `indent` debug (unparseProp prop)
        return $ map (fmap $ generalizeExceptProp recVars) pcHyps
      where
        instOver n = [(over, Free n)]

checkProof prop (ParseCompInduction funRaw oversRaw casesRaw) env = errCtxt ctxtMsg $ do
    flip evalStateT env $ do
        overs <- forM oversRaw validateOver
        env <- get
        lift $ validateCases overs casesRaw env
        return prop
    where
        ctxtMsg = "Induction on the computation of" <+> quotes (text funRaw)

        validateOver t = do
            t' <- state (declareTerm $ Free t)
            case t' of
                Free v -> return v
                _ -> lift $ err $ "Term" <+> quotes (unparseTerm t') <+> "is not a valid induction variable"

        funEqs = namedVal <$> filter (\namedProp -> namedName namedProp == "def " ++ funRaw) (axioms env)
        funArity = length $ snd $ stripComb $ propLhs $ head funEqs

        validateCases overs cases env = do
            caseNums <- traverse (validateCase overs env) cases
            case missingCase caseNums of
                Nothing -> return ()
                Just caseNum -> err $ "Missing case" <+> int caseNum
            where
                missingCase caseNums = find (`notElem` caseNums) [1..length funEqs]

        validateCase overs env ParseCompCase{pccCaseNum = caseNum, pccBody = pcb}
            | null funEqs = err $ hsep ["The function", quotes (text funRaw), "does not exist"]
            | length overs < funArity = err $ hsep ["Fewer variables than arity of function", quotes (text funRaw), "given"]
            | length overs > funArity = err $ hsep ["More variables than arity of function", quotes (text funRaw), "given"]
            | caseNum < 1 = err "Case number must be at least 1"
            | caseNum > length funEqs =
                err $ hsep [ "The function", quotes (text funRaw), "has", int (length funEqs)
                           , "equations but got case number", int caseNum ]
            | otherwise = errCtxt (text "Case" <+> int caseNum) $ flip evalStateT env $ do
                let funEq = funEqs !! (caseNum - 1)
                let (_, funEqInsts) = stripComb (propLhs funEq)

                let schematicSubgoal = substFreeProp prop $ zip overs funEqInsts

                case pcbToShow pcb of
                    Nothing -> lift $ errStr "Missing 'To show'"
                    Just rawToShow -> do
                        toShow <- state (declareProp rawToShow)
                        case matchProp toShow schematicSubgoal [] of
                            Nothing -> lift . err $
                                           "'To show' does not match subgoal:"
                                           `indent` (
                                                "To show:" <+> unparseProp toShow $+$
                                                debug ("Subgoal:" <+> unparseProp schematicSubgoal))
                            Just unifier -> do
                                let subgoal = substProp schematicSubgoal unifier
                                userHyps <- checkPcHyps overs (recArgs $ subst (propRhs funEq) unifier) $ pcbAssms pcb
                                modify (\env -> env{axioms = userHyps ++ axioms env})
                                env <- get
                                Prop _ _ <- lift $ checkProof subgoal (pcbProof pcb) env
                                return caseNum

        recArgs t@(Application _ _)
            | t0 == Const symIf = []
            | t0 == Const funRaw = ts : concatMap recArgs ts
            | otherwise = concatMap recArgs ts
            where
                (t0, ts) = stripComb t
        recArgs _ = []

        checkPcHyps overs recArgs rpcHyps = do
            pcHyps <- traverse (traverse (state . declareProp)) rpcHyps
            let indHyps = substFreeProp prop . zip overs <$> recArgs

            lift $ forM pcHyps $ \(Named name prop) ->
                case prop `elemIndex` indHyps of
                    Just i -> return $ Named name $ generalizeExceptProp (foldr collectFrees [] (recArgs !! i)) prop
                    Nothing -> err $ ("Induction hypothesis" <+> text name <+> "is not valid")
                                     `indent` debug (unparseProp prop)

checkProof prop (ParseCases dtRaw onRaw casesRaw) env = errCtxt ctxtMsg $ do
    dt <- validDatatype dtRaw env
    flip evalStateT env $ do
        on <- state (declareTerm onRaw)
        env <- get
        lift $ validateCases dt on casesRaw env
        return prop
  where
    ctxtMsg = text "Case analyis on"
        <+> quotes (unparseRawTerm onRaw) <+> text "of type" <+> quotes (text dtRaw)

    -- duplicated code from ParseInduction
    validateCases dt on cases env = do
        caseNames <- traverse (validateCase dt on env) cases
        case missingCase caseNames of
            Nothing -> return ()
            Just (name, _) -> errStr $ "Missing case '" ++ name ++ "'"
      where
        missingCase caseNames = find (\(name, _) -> name `notElem` caseNames) (dtConss dt)

    validateCase dt on env ParseCase{pcCons = pcc, pcBody = pcb} = errCtxt (text "Case" <+> quotes (unparseRawTerm pcc)) $ do
        flip evalStateT env $ do
            caseT <- state (variantFixesTerm pcc)
            (consName, _) <- lift $ validConsCase caseT dt

            when (isJust $ pcbToShow pcb) $
                lift $ errStr "Superfluous 'To show'"

            userAssm <- checkPcAssms on caseT $ pcbAssms pcb

            modify (\env -> env { axioms = userAssm : axioms env })
            env <- get
            Prop _ _ <- lift $ checkProof prop (pcbProof pcb) env
            return consName

    checkPcAssms :: Term -> Term -> [Named RawProp] -> StateT Env Err (Named Prop)
    checkPcAssms on caseT [Named name rawProp] = do
        prop <- state (declareProp rawProp)
        let Prop lhs rhs = prop
        when (lhs /= on) $ bail "Invalid left-hand side of assumption, expected:" on
        when (rhs /= caseT) $ bail "Invalid right-hand side of assumption, expected:" caseT
        return $ Named name prop
      where
        bail msg t = lift $ err $ text msg <+> quotes (unparseTerm t)
    checkPcAssms _ _ _ = lift $ errStr "Expected exactly one assumption"


validDatatype :: String -> Env -> Err DataType
validDatatype name env = case find (\dt -> dtName dt == name) (datatypes env) of
    Nothing -> err $ fsep $
        [ text "Invalid datatype" <+> quotes (text name) Text.PrettyPrint.<> text "."
        , text "Expected one of:" ]
        ++ punctuate comma (map (quotes . text . dtName) $ datatypes env)
    Just dt -> Right dt

validConsCase :: Term -> DataType -> Err (String, [(TConsArg, IdxName)])
validConsCase t (DataType _ conss) = errCtxt invCaseMsg $ do
    (consName, consArgs) <- findCons cons
    argNames <- traverse argName args
    unless (nub args == args) $
        errStr "Constructor arguments must be distinct"
    unless (length args == length consArgs) $
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

    invCaseMsg = text "Invalid case" <+> quotes (unparseTerm t) Text.PrettyPrint.<> comma

validEqnSeq :: [Named Prop] -> EqnSeq Term -> Err Prop
validEqnSeq _ (Single t) = return (Prop t t)
validEqnSeq rules (Step spos t1 rule es)
    | rewritesToWith rule rules t1 t2 = do
        Prop _ tLast <- validEqnSeq rules es
        return (Prop t1 tLast)
    | otherwise = errCtxtStr (showSrcPos spos ++ " Invalid proof step" ++ noRuleMsg) $ err $
        unparseTerm t1 $+$ text ("(by " ++ rule ++ ") " ++ symPropEq) <+> unparseTerm t2
        $+$ debug (text rule Text.PrettyPrint.<> text ":" <+> vcat (map (unparseProp . namedVal) $ filter (\x -> namedName x == rule) rules))
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
    if tl1 == tl2 then return (Prop th1 th2)
    else errCtxtStr "Two equation chains don't fit together:" $
            err $ unparseTerm tl1 $+$ text symPropEq $+$ unparseTerm tl2

rewriteTop :: Term -> Prop -> Maybe Term
rewriteTop t (Prop lhs rhs) = subst rhs <$> match t lhs []

rewrite :: Term -> Prop -> [Term]
rewrite t@(Application f a) prop =
    maybeToList (rewriteTop t prop)
    ++ map (`Application` a) (rewrite f prop)
    ++ map (Application f) (rewrite a prop)
rewrite t prop = maybeToList $ rewriteTop t prop

rewritesTo :: [Prop] -> Term -> Term -> Bool
rewritesTo rules l r = l == r || rewrites l r || rewrites r l
  where rewrites from to = any (\x -> isJust $ match to x []) $ concatMap (rewrite from) rules

rewritesToWith :: String -> [Named Prop] -> Term -> Term -> Bool
rewritesToWith name rules = rewritesTo (f rules)
  where f = map namedVal . filter (\x -> namedName x == name)
