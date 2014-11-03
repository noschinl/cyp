module Test.Info2.Cyp (
  proof
, proofFile
, Err
) where

import Data.Char
import Control.Applicative (pure, (<$>), (<*>))
import Control.Monad
import Data.Foldable (Foldable, foldMap, for_)
import Data.List
import Data.Maybe
import Data.Monoid (mappend)
import Data.Traversable (Traversable, traverse)
import Text.Parsec as Parsec
import qualified Language.Haskell.Exts.Parser as P
import qualified Language.Haskell.Exts.Syntax as Exts
import Text.PrettyPrint (comma, fsep, punctuate, quotes, text, vcat, (<>), (<+>), ($+$), render)

import Test.Info2.Cyp.Term
--import Test.Info2.Cyp.Trace
import Test.Info2.Cyp.Util

data ParseDeclTree
    = DataDecl String
    | SymDecl String
    | Axiom String String
    | FunDef String
    | Goal String
    deriving Show

data ParseLemma = ParseLemma String Prop ParseProof -- Proposition, Proof

data ParseCase = ParseCase
    { pcCons :: Term
    , pcToShow :: Prop
    , pcIndHyps :: [Named Prop]
    , pcEqns :: ParseProof
    }

data ParseProof
    = ParseInduction String String [ParseCase] -- DataTyp, Over, Cases
    | ParseEquation (EqnSeqq Term)

data Env = Env
    { datatypes :: [DataType]
    , axioms :: [Named Prop]
    , constants :: [String]
    , goals :: [Prop]
    }
    deriving Show

data DataType = DataType String [(String, [TConsArg])] -- name cases
    deriving (Show)

data Named a = Named String a
    deriving Show

data Proof
    = Induction DataType String [(String, [Term])] -- typ ,ind var, ...
    | Equation [Term]
    deriving (Show)

data Lemma = Lemma Prop Proof -- Proposition (_ = _), Proof
    deriving (Show)

data EqnSeq a = Single a | Step a String (EqnSeq a)
data EqnSeqq a = EqnSeqq (EqnSeq a) (Maybe (EqnSeq a))

data TConsArg = TNRec | TRec deriving (Show,Eq)


{- Default constants -------------------------------------------------}

defConsts :: [String]
defConsts = [symPropEq]

{- Equation sequences ------------------------------------------------}

instance Foldable EqnSeq where
    foldMap f (Single x) = f x
    foldMap f (Step x _ es) = f x `mappend` foldMap f es

instance Functor EqnSeq where
    fmap f (Single x) = Single (f x)
    fmap f (Step x y es) = Step (f x) y (fmap f es)

instance Traversable EqnSeq where
    traverse f (Single x) = Single <$> f x
    traverse f (Step x y es) = Step <$> f x <*> pure y <*> traverse f es

-- Functor instance?
mapEqnSeqq :: (a -> a) -> EqnSeqq a -> EqnSeqq a
mapEqnSeqq f (EqnSeqq x y) = EqnSeqq (fmap f x) (fmap f <$> y)


eqnSeqFromList :: a -> [(String,a)] -> EqnSeq a
eqnSeqFromList a [] = Single a
eqnSeqFromList a ((b', a') : bas) = Step a b' (eqnSeqFromList a' bas)

eqnSeqEnds :: EqnSeq a -> (a,a)
eqnSeqEnds (Single x) = (x,x)
eqnSeqEnds (Step a _ es) = (a, snd $ eqnSeqEnds es)


{- Named operations --------------------------------------------------}

instance Functor Named where
    fmap f (Named n x) = Named n (f x)

namedVal :: Named a -> a
namedVal (Named _ a) = a

namedName :: Named a -> String
namedName (Named name _) = name


{- Main -------------------------------------------------------------}

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
    mResult <- eitherToErr $ Parsec.parse masterParser path content
    dts <- readDataType mResult
    syms <- readSym mResult
    (fundefs, consts) <- readFunc syms mResult
    axs <- readAxiom consts mResult
    gls <- readGoal consts mResult
    return $ Env { datatypes = dts, axioms = fundefs ++ axs,
        constants = nub $ defConsts ++ consts, goals = gls }

processProofFile :: Env -> FilePath -> String -> Err [ParseLemma]
processProofFile env path  content= errCtxtStr "Parsing proof" $
    eitherToErr $ Parsec.runParser studentParser env path content

checkProofs :: Env -> [ParseLemma] -> Err [Named Prop]
checkProofs env []  = Right $ axioms env
checkProofs env (l@(ParseLemma name prop _) : ls) = do
    errCtxt (text "Lemma:" <+> unparseProp prop) $
        checkProof env l
    checkProofs (env { axioms = Named name prop : axioms env }) ls

checkProof :: Env -> ParseLemma -> Err ()
checkProof env (ParseLemma _ prop (ParseEquation eqns)) = errCtxtStr "Equational proof" $ do
    validEquationProof (axioms env) eqns prop
    return ()
checkProof env (ParseLemma _ prop (ParseInduction dtRaw overRaw casesRaw)) = errCtxt ctxtMsg $ do
    dt <- validateDatatype dtRaw
    over <- validateOver overRaw
    validateCases dt over casesRaw
  where
    ctxtMsg = text "Induction over variable"
        <+> quotes (text overRaw) <+> text "of type" <+> quotes (text dtRaw)

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

    validateCase :: DataType -> String -> ParseCase -> Err String
    validateCase dt over pc = errCtxt (text "Case" <+> quotes (unparseTerm $ pcCons pc)) $ do
        (consName, consArgNs) <- lookupCons (pcCons pc) dt
        let argsNames = map snd consArgNs

        let subgoal = substProp prop [(over, pcCons pc)]
        let toShow = generalizeExceptProp argsNames $ pcToShow pc
        when (subgoal /= toShow) $ err
             $ text "'To show' does not match subgoal:"
             `indent` (text "To show: " <+> unparseProp toShow)

        let indHyps = map (substProp prop . instOver) . filter (\x -> fst x == TRec) $ consArgNs

        userHyps <- checkPcHyps argsNames indHyps $ pcIndHyps pc

        let ParseEquation eqns = pcEqns pc -- XXX
        let eqns' = generalizeExcept argsNames `mapEqnSeqq` eqns

        eqnProp <- validEquationProof (userHyps ++ axioms env) eqns' subgoal
        when (eqnProp /= toShow) $
            err $ (text "Result of equational proof" `indent` (unparseProp eqnProp))
                $+$ (text "does not match stated goal:" `indent` (unparseProp toShow))
        return consName
      where
        instOver (_, n) = [(over, Free n)]

    checkPcHyps :: [String] -> [Prop] -> [Named Prop] -> Err [Named Prop]
    checkPcHyps instVars indHyps pcHyps = do
        let inst = map (\v -> (v, Free v)) instVars
        let userHyps = map (fmap (flip substProp inst)) $ pcHyps
        for_ userHyps $ \(Named name prop) -> case prop `elem` indHyps of
            True -> return ()
            False -> err $ text $ "Induction hypothesis " ++ name ++ " is not valid"
        return userHyps

    validateDatatype name = case find (\dt -> getDtName dt == name) (datatypes env) of
        Nothing -> err $ fsep $
            [ text "Invalid datatype" <+> quotes (text name) <> text "."
            , text "Expected one of:" ]
            ++ punctuate comma (map (quotes . text . getDtName) $ datatypes env)
        Just dt -> Right dt

    validateOver s = do
        term <- iparseTerm (defaultToFree $ constants env) s
        case term of
            Free v -> return v
            _ -> err $ text "Term" <+> quotes (text s)
                <+> text "is not a valid induction variable"

    validateCases dt over cases = do
        caseNames <- traverse (validateCase dt over) cases
        case missingCase caseNames of
            Nothing -> return ()
            Just (name, _) -> errStr $ "Missing case '" ++ name ++ "'"
      where
        missingCase caseNames = find (\(name, _) -> name `notElem` caseNames) (getDtConss dt)

    getDtConss (DataType _ conss) = conss
    getDtName (DataType n _) = n

validEqnSeq :: [Named Prop] -> EqnSeq Term -> Err (Term, Term)
validEqnSeq _ (Single t) = return (t, t)
validEqnSeq rules (Step t1 rule es)
    | rewritesToWith rule rules t1 t2 = do
        (_, tLast) <- validEqnSeq rules es
        return (t1, tLast)
    | otherwise = errCtxtStr ("Invalid proof step" ++ noRuleMsg) $
        err $ unparseTerm t1 $+$ text ("(by " ++ rule ++ ") " ++ symPropEq) <+> unparseTerm t2
  where
    (t2, _) = eqnSeqEnds es
    noRuleMsg
        | any (\x -> namedName x == rule) rules = ""
        | otherwise = " (no rules with name \"" ++ rule ++ "\")"

validEqnSeqq :: [Named Prop] -> EqnSeqq Term -> Err (Term, Term)
validEqnSeqq rules (EqnSeqq es1 Nothing) = validEqnSeq rules es1
validEqnSeqq rules (EqnSeqq es1 (Just es2)) = do
    (th1, tl1) <- validEqnSeq rules es1
    (th2, tl2) <- validEqnSeq rules es2
    case tl1 == tl2 of
        True -> return (th1, th2)
        False -> errCtxtStr "Two equation chains don't fit together:" $
            err $ unparseTerm tl1 $+$ text symPropEq $+$ unparseTerm tl2

validEquationProof :: [Named Prop] -> EqnSeqq Term -> Prop -> Err Prop
validEquationProof rules eqns goal = do
    (l,r) <- validEqnSeqq rules eqns
    let prop = Prop l r
    case isFixedProp prop $ goal of
        False -> err $ text "Proved proposition does not match goal:"
                     `indent` (unparseProp prop)
        True -> return prop

-- XXX Think about schemFrees again ...
isFixedProp :: Prop -> Prop -> Bool
isFixedProp fixedProp schemProp = isJust $ do
    inst <- map snd <$> matchProp fixedProp schemProp []
    --let (Prop schemL schemR) = schemProp
    --let schemFrees = collectFrees schemL $ collectFrees schemR $ []
    guard $ all (\x -> isFree x || isSchematic x) inst && nub inst == inst -- && null schemFrees

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


readDataType :: [ParseDeclTree] -> Err [DataType]
readDataType = sequence . mapMaybe parseDataType
  where
    parseDataType (DataDecl s) = Just $ errCtxt (text "Parsing the datatype declaration" <+> quotes (text s)) $ do
        (tycon : dacons) <- traverse parseCons $ splitStringAt "=|" s []
        tyname <- constName $ fst $ stripComb tycon
        dacons' <- traverse (parseDacon tycon) dacons
        return $ DataType tyname dacons'
    parseDataType _ = Nothing

    parseCons :: String -> Err Term
    parseCons = iparseTerm (Right . Free)

    constName (Const c) = return c
    constName term = errStr $ "Term '" ++ show term ++ "' is not a constant."

    parseDacon tycon term = do
        let (con, args) = stripComb term
        name <- constName con
        args' <- traverse (parseDaconArg tycon) args
        return (name, args')

    parseDaconArg tycon term | term == tycon = return TRec
    parseDaconArg _ (Application _ _) = errStr $ "Nested constructors (apart from direct recursion) are not allowed."
    parseDaconArg _ (Literal _) = errStr $ "Literals not allowed in datatype declarations"
    parseDaconArg _ _ = return TNRec

readAxiom :: [String] -> [ParseDeclTree] -> Err [Named Prop]
readAxiom consts = sequence . mapMaybe parseAxiom
  where
    parseAxiom (Axiom n s) = Just (Named n <$> iparseProp (defaultToSchematic consts) s)
    parseAxiom _ = Nothing

readGoal :: [String] -> [ParseDeclTree] -> Err [Prop]
readGoal consts = sequence . mapMaybe parseGoal
  where
    parseGoal (Goal s) = Just $ iparseProp (defaultToFree consts) s
    parseGoal _ = Nothing

readSym :: [ParseDeclTree] -> Err [String]
readSym = sequence . mapMaybe parseSym
  where
    parseSym (SymDecl s) = Just $ do
        term <- iparseTerm (Right . Const) s
        case term of
            Const v -> Right v
            _ -> errStr $ "Expression '" ++ s ++ "' is not a symbol"
    parseSym _ = Nothing


readFunc :: [String] -> [ParseDeclTree] -> Err ([Named Prop], [String])
readFunc syms pds = do
    rawDecls <- sequence . mapMaybe parseFunc $ pds
    let syms' = syms ++ map (\(sym, _, _) -> sym) rawDecls
    props <- traverse (declToProp syms') rawDecls
    return (props, syms')
  where

    declToProp :: [String] -> (String, [Exts.Pat], Exts.Exp) -> Err (Named Prop)
    declToProp consts (funSym, pats, rawRhs) = do
        tPat <- traverse translatePat pats
        rhs <- translateExp tv rawRhs
        return $ Named ("def " ++ funSym) $ Prop (listComb (Const funSym) tPat) rhs
      where
        pvars = concatMap collectPVars pats
        tv s | s `elem` pvars = return $ Schematic s
             | s `elem` consts = return $ Const s
             | otherwise = errStr $ "Unbound variable '" ++ s ++ "' not allowed on rhs"

    collectPVars :: Exts.Pat -> [String]
    collectPVars (Exts.PVar v) = [translateName v]
    collectPVars (Exts.PInfixApp p1 _ p2) = collectPVars p1 ++ collectPVars p2
    collectPVars (Exts.PApp _ ps) = concatMap collectPVars ps
    collectPVars (Exts.PList ps) = concatMap collectPVars ps
    collectPVars (Exts.PParen p) = collectPVars p
    collectPVars _ = []

    parseFunc :: ParseDeclTree -> Maybe (Err (String, [Exts.Pat], Exts.Exp))
    parseFunc (FunDef s) = Just $ errCtxt (text "Parsing function definition" <+> quotes (text s)) $
        case P.parseDecl s of
            P.ParseOk (Exts.FunBind [Exts.Match _ name pat _ (Exts.UnGuardedRhs rhs) (Exts.BDecls [])])
                -> Right (translateName name, pat, rhs)
            P.ParseOk _ -> errStr "Invalid function definition."
            f@(P.ParseFailed _ _ ) -> errStr $ show f
    parseFunc _ = Nothing

splitStringAt :: Eq a => [a] -> [a] -> [a] -> [[a]]
splitStringAt _ [] h
    | h == [] = []
    | otherwise = h : []
splitStringAt a (x:xs) h
    | x `elem` a = h : splitStringAt a xs []
    | otherwise = splitStringAt a xs (h++[x])


{- Parser for the outer syntax --------------------------------------}

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

toParsec :: (a -> String) -> Either a b -> Parsec c u b
toParsec f = either (fail . f) return

eol :: Parsec [Char] u ()
eol = do
    _ <- try (string "\n\r") <|> try (string "\r\n") <|> string "\n" <|> string "\r" -- <|> (eof >> return "")
        <?> "end of line"
    return ()

idParser :: Parsec [Char] u String
idParser = idP <?> "Id"
  where
    idP = do
        c <- lower
        cs <- many (char '_' <|> alphaNum)
        lineSpaces
        return (c:cs)

commentParser :: Parsec [Char] u ()
commentParser =
    do  _ <- string "--"
        _ <- many (noneOf "\r\n")
        eol <|> eof
        return ()
longcommentParser :: Parsec [Char] u ()
longcommentParser =
    do  _ <- string "{-"
        _ <- manyTill anyChar (try (string "-}"))
        return ()

commentParsers :: Parsec [Char] u ()
commentParsers = commentParser <|> longcommentParser <?> "comment"

masterParser :: Parsec [Char] () [ParseDeclTree]
masterParser =
    do result <- many masterParsers
       eof
       return result

masterParsers :: Parsec [Char] () ParseDeclTree
masterParsers =
    do manySpacesOrComment
       result <- (goalParser <|> dataParser <|> axiomParser <|> symParser <|> try funParser)
       return result

keywordToEolParser :: String -> (String -> a) -> Parsec [Char] () a
keywordToEolParser s f =
    do  keyword s
        result <- trim <$> toEol
        return (f result)

axiomParser :: Parsec [Char] () ParseDeclTree
axiomParser = do
    keyword "axiom"
    name <- idParser
    char ':'
    xs <- trim <$> toEol
    return $ Axiom name xs

dataParser :: Parsec [Char] () ParseDeclTree
dataParser = keywordToEolParser "data" DataDecl

goalParser :: Parsec [Char] () ParseDeclTree
goalParser = keywordToEolParser "goal" Goal

symParser :: Parsec [Char] () ParseDeclTree
symParser = keywordToEolParser "declare_sym" SymDecl

funParser :: Parsec [Char] () ParseDeclTree
funParser =
    do  c <- noneOf "\r\n"
        cs <- toEol
        return (FunDef $ c:cs)

equationProofParser :: Parsec [Char] Env ParseProof
equationProofParser = do
    keyword "Proof"
    eqns <- equationsParser
    manySpacesOrComment
    keywordQED
    return $ ParseEquation eqns

inductionProofParser :: Parsec [Char] Env ParseProof
inductionProofParser =
    do  keyword "Proof by induction on"
        datatype <- many (noneOf " \t")
        lineSpaces
        over <- toEol
        manySpacesOrComment
        cases <- many1 caseParser
        manySpacesOrComment
        keywordQED
        return (ParseInduction datatype over cases)

type PropParserMode = [String] -> String -> Err Term

propParser :: PropParserMode -> Parsec [Char] Env Prop
propParser mode = do
    s <- trim <$> toEol1
    env <- getState
    let prop = errCtxtStr "Failed to parse expression" $
            iparseProp (mode $ constants env) s
    toParsec show prop

termParser :: PropParserMode -> Parsec [Char] Env Term
termParser mode = do
    s <- trim <$> toEol1
    env <- getState
    let term = errCtxtStr "Failed to parse expression" $
            iparseTerm (mode $ constants env) s
    toParsec show term

namedPropParser :: PropParserMode -> Parsec [Char] Env String -> Parsec [Char] Env (String, Prop)
namedPropParser mode p = do
    name <- option "" p
    char ':'
    prop <- propParser mode
    return (name, prop)

lemmaParser :: Parsec [Char] Env ParseLemma
lemmaParser =
    do  keyword "Lemma"
        (name, prop) <- namedPropParser defaultToSchematic idParser
        manySpacesOrComment
        prf <- inductionProofParser <|> equationProofParser
        manySpacesOrComment
        return $ ParseLemma name prop prf

studentParser ::  Parsec [Char] Env [ParseLemma]
studentParser =
    do  lemmas <- many1 lemmaParser
        eof
        return lemmas

lineSpaces :: Parsec [Char] u ()
lineSpaces = skipMany (oneOf " \t") <?> "horizontal white space"

keyword :: String -> Parsec [Char] u ()
keyword kw = try $ do
    _ <- string kw
    notFollowedBy alphaNum
    lineSpaces

keywordCase :: Parsec [Char] u ()
keywordCase = keyword "Case"

keywordQED :: Parsec [Char] u ()
keywordQED = keyword "QED"

toEol :: Parsec [Char] u String
toEol = manyTill anyChar (eof <|> try eol <|> try commentParser)

toEol1 :: Parsec [Char] u String
toEol1 = do
    cs <- toEol
    case cs of
        [] -> unexpected "missing text before eol or comment"
        _ -> return cs

byRuleParser :: Parsec [Char] u String
byRuleParser = do
    char '(' >> lineSpaces
    keyword "by"
    cs <- trim <$> manyTill (noneOf "\r\n") (char ')')
    lineSpaces
    return cs

equationsParser :: Parsec [Char] Env (EqnSeqq Term)
equationsParser = do
    eq1 <- equations'
    eq2 <- optionMaybe (try equations')
    return $ EqnSeqq eq1 eq2
  where
    equations' = do
        spaces
        eq <- termParser defaultToFree
        eqs <- many1 (try eqnStep)
        return $ eqnSeqFromList eq eqs
    eqnStep = do
        manySpacesOrComment
        rule <- byRuleParser
        string symPropEq
        lineSpaces
        eq <- termParser defaultToFree
        return (rule, eq)

caseParser :: Parsec [Char] Env ParseCase
caseParser = do
    keywordCase
    lineSpaces
    t <- termParser defaultToFree
    manySpacesOrComment
    toShow <- toShowP
    manySpacesOrComment
    indHyps <- indHypsP
    manySpacesOrComment
    eqnPrf <- equationProofParser
    manySpacesOrComment
    return $ ParseCase
        { pcCons = t
        , pcToShow = toShow
        , pcIndHyps = indHyps
        , pcEqns = eqnPrf
        }
  where
    toShowP = do
        keyword "To show"
        lineSpaces
        char ':'
        propParser defaultToFree
    indHypsP = many $ do
        hyp <- indHypP
        manySpacesOrComment
        return hyp
    indHypP = do
        string "IH"
        spaces
        (name, prop) <- namedPropParser defaultToSchematic (many alphaNum)
        return $ Named (if name == "" then "IH" else "IH " ++ name) prop


manySpacesOrComment :: Parsec [Char] u ()
manySpacesOrComment = skipMany $ (space >> return ()) <|> commentParsers
