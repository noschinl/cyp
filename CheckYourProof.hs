module CheckYourProof where
import Data.Char
import Control.Applicative ((<$>))
import Control.Monad
import Data.List
import Data.Maybe
import Data.Foldable (traverse_)
import Data.Traversable (traverse)
import Text.Parsec as Parsec
import Language.Haskell.Exts.Parser 
import Language.Haskell.Exts.Fixity
import qualified Language.Haskell.Exts.Syntax as Exts
import Language.Haskell.Exts.Syntax (Literal (..), QName(..), SpecialCon (..), Name (..), ModuleName (..), Exp (..), QOp (..), Assoc(..))
import Debug.Trace
import Text.Show.Pretty (ppShow)

{-

This software is released under the BSD3 license.

Copyright (c) 2013 Dominik Durner (Wiesbachstraße 5, 86529 Schrobenhausen, Germany) 
	& Lars Noschinski (Boltzmannstr. 3, 85748 Garching, Germany)
    & TU München, Institut for Informatics, Chair for Logic and Verification (I21) 
    	(Boltzmannstr. 3, 85748 Garching, Germany)
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the TU München nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL COPYRIGHT HOLDER BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.



Check Your Proof (CYP)
    What is CYP?
        Check your Proof is a functional program for students to check the correctness of their 
            proofs by induction over simple data structures (e.g. List, Trees)
-}

type ConstList = [String]
type VariableList = [String]

data ParseDeclTree
    = DataDecl String
    | SymDecl String
    | Axiom String
    | FunDef String
    deriving Show

data ParseLemma = ParseLemma Prop ParseProof deriving Show -- Proposition, Proof

data ParseProof
    = ParseInduction String String [(String, [Cyp])] -- DataTyp, Over, Cases
    | ParseEquation [Cyp]
    deriving Show

type ParseEquations = [String]

data Env = Env
    { datatypes :: [DataType]
    , axioms :: [Prop]
    , constants :: [String]
    }
    deriving Show

data DataType = DataType String [(String, [TConsArg])] -- name cases
    deriving (Show)

data Prop = Prop Cyp Cyp
    deriving (Eq, Show) -- lhs, rhs

data Proof
    = Induction DataType String [(String, [Cyp])] -- typ ,ind var, ...
    | Equation [Cyp]
    deriving (Show)

data Lemma = Lemma Prop Proof -- Proposition (_ = _), Proof
    deriving (Show)


data Cyp = Application Cyp Cyp | Const String | Variable String | Literal Literal
    deriving (Show, Eq)

data TConsArg = TNRec | TRec deriving (Show,Eq)


{- Debug tools ------------------------------------------------------}

tracePretty :: Show a => a -> b -> b
tracePretty = trace . ppShow

tracePrettyA :: Show a => a -> a
tracePrettyA x = tracePretty x x

tracePrettyF :: Show b => (a -> b) -> a -> a
tracePrettyF f x = tracePretty (f x) x

printRunnable :: Cyp -> String
printRunnable (Application cypCurry cyp) = "(" ++ (printRunnable cypCurry) ++ " " ++ (printRunnable cyp) ++ ")"
printRunnable (Literal a) = translateLiteral a
printRunnable (Variable a) = a
printRunnable (Const a) = a


{- Cyp operations ---------------------------------------------------}

mApp :: Monad m => m Cyp -> m Cyp -> m Cyp
mApp = liftM2 Application

infixl 1 `mApp`
infixl 1 `Application`


{- Prop operations --------------------------------------------------}

mapProp :: (Cyp -> Cyp) -> Prop -> Prop
mapProp f (Prop l r) = Prop (f l) (f r)



{- Main -------------------------------------------------------------}

proof :: FilePath-> FilePath -> IO (Either String [Prop])
proof masterFile studentFile = do
    mContent <- readFile masterFile
    sContent <- readFile studentFile
    let env = do
        mResult <- showLeft $ Parsec.parse masterParser masterFile mContent
        dts <- readDataType mResult
        syms <- readSym mResult
        (fundefs, consts) <- readFunc syms mResult
        axs <- readAxiom consts mResult
        return $ Env { datatypes = dts, axioms = fundefs ++ axs , constants = nub consts }
    let lemmas = do
        e <- env
        showLeft $ Parsec.runParser studentParser e studentFile sContent
    return $ join $ liftM2 process env lemmas
  where
    showLeft (Left x) = Left (show x)
    showLeft (Right x) = Right x

    process env lemmas = checkProofs env lemmas

checkProofs :: Env-> [ParseLemma] -> Either String [Prop]
checkProofs env []  = Right $ axioms env
checkProofs env (l@(ParseLemma prop _) : ls) = do
    checkProof env l
    checkProofs (env { axioms = prop : axioms env}) ls

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

checkProof :: Env -> ParseLemma -> Either String ()
checkProof env (ParseLemma prop (ParseEquation eqns)) = validEquationProof (axioms env) eqns prop
checkProof env (ParseLemma prop (ParseInduction dtRaw overRaw casesRaw)) = do
    dt <- validateDatatype dtRaw
    over <- validateOver overRaw
    validateCases dt over casesRaw
  where
    lookupCons name (DataType _ conss) = maybe (Left $ "Invalid case '" ++ name ++ "'") Right $
        find (\c -> fst c == name) conss >>= return

    validateCase dt over (name, steps) = mapLeft (\x -> "Error in case '" ++ name ++"':\n    " ++ x) $do
        cons <- lookupCons name dt
        (indHyps, fixVars) <- computeIndHyps prop steps over cons
        validEquations (indHyps ++ axioms env) $ map (\x -> transformVarToConstList x fixVars) steps

    transformVarToConstList :: Cyp -> [String] -> Cyp
    transformVarToConstList cyp = subst cyp . map (\x -> (x, Const x))

    validateDatatype name = case find (\dt -> getDtName dt == name) (datatypes env) of
        Nothing -> Left $  "Invalid datatype '" ++ name ++ "'. Expected one of "
            ++ show (map getDtName $ datatypes env)
        Just dt -> Right dt

    validateOver text = do
        cyp <- iparseCyp env text
        case cyp of
            Variable v -> return v
            _ -> Left $ "Variable '" ++ text ++ "' is not a valid induction variable"

    validateCases dt over cases = do
        case missingCase of
            Nothing -> return ()
            Just (name, _) -> Left $ "Missing case '" ++ name ++ "'"
        traverse_ (validateCase dt over) cases
      where
        caseNames = map fst cases
        missingCase = find (\(name, _) -> name `notElem` caseNames) (getDtConss dt)

    getDtConss (DataType _ conss) = conss
    getDtName (DataType n _) = n

validEquations :: [Prop] -> [Cyp] -> Either String ()
validEquations _ [] = Left "Empty equation sequence"
validEquations _ [_] = Right ()
validEquations rules (t1:t2:ts)
    | t2 `elem` rewriteAll t1 rules = validEquations rules (t2:ts)
    | otherwise = Left $ "(nmr) No matching rule: step " ++ printInfo t1 ++ " to " ++ printInfo t2

validEquationProof :: [Prop] -> [Cyp] -> Prop -> Either String ()
validEquationProof rules eqns aim = do
    validEquations rules eqns
    let proved = Prop (head eqns) (last eqns)
    if proved == aim
        then Right ()
        else Left ("Proved proposition does not match goal:\n" ++ printProp proved ++ "\nvs.\n" ++ printProp aim)

match :: Cyp -> Cyp -> [(String, Cyp)] -> Maybe [(String, Cyp)]
match (Application f a) (Application f' a') s = match f f' s >>= match a a'
match (Literal a) (Literal b) s
    | a == b = Just s
    | otherwise = Nothing
match (Const a) (Const b) s
    | a == b = Just s
    | otherwise = Nothing
match t (Variable v) s = case lookup v s of
    Nothing -> Just $ (v,t) : s
    Just t' -> if t == t' then Just s else Nothing
match _ _ _ = Nothing

matchProp :: Prop -> Prop -> [(String, Cyp)] -> Maybe [(String, Cyp)]
matchProp (Prop l r) (Prop l' r') s = match l l' s >>= match r r'

subst :: Cyp -> [(String, Cyp)] -> Cyp
subst (Application f a) s = Application (subst f s) (subst a s)
subst (Variable v) s = case lookup v s of
      Nothing -> Variable v
      Just t -> t
subst t _ = t

substProp :: Prop -> [(String, Cyp)] -> Prop
substProp prop s = mapProp (\c -> subst c s) prop

rewriteTop :: Cyp -> Prop -> Maybe Cyp
rewriteTop t (Prop lhs rhs) = fmap (subst rhs) $ match t lhs []

rewrite :: Cyp -> Prop -> [Cyp]
rewrite t@(Application f a) prop =
    maybeToList (rewriteTop t prop)
    ++ map (\x -> Application x a) (rewrite f prop)
    ++ map (Application f) (rewrite a prop)
rewrite t prop = maybeToList $ rewriteTop t prop

-- XXX: move reflexivity out of rewriteAll, it is unexpected here ...
rewriteAll :: Cyp -> [Prop] -> [Cyp]
rewriteAll cyp rules = cyp : concatMap (rewrite cyp) rules'
    where rules' = rules ++ map (\(Prop l r) -> Prop r l) rules

computeIndHyps :: Prop -> [Cyp] -> String -> (String, [TConsArg]) -> Either String ([Prop], [String])
computeIndHyps prop step over con = do
    inst <- maybe (Left "Equations do not match induction hypothesis") Right $
        matchInductVar prop $ Prop (head step) (last step)
    (recVars, nonrecVars) <- matchInstWithCon con (stripComb inst)
    let instVars = recVars ++ nonrecVars
    when (nub instVars /= instVars) $
        Left "The induction variables must be distinct!"
    let indHyps = map (\v -> substProp prop [(over, Const v)]) recVars
    return (indHyps, instVars)
  where
    matchInductVar :: Prop -> Prop -> Maybe Cyp
    matchInductVar pat cyp = do
        s <- matchProp cyp pat []
        guard $ instOnly over s
        lookup over s
      where instOnly x = all (\(var,inst) -> var == x || Variable var == inst)

    matchInstWithCon :: (String, [TConsArg]) -> (Cyp, [Cyp]) -> Either String ([String], [String])
    matchInstWithCon (conName, conArgs) (f, args)
        | Const conName /= f = Left $ "Equations and case do not match: "
            ++ show (Const conName) ++ " vs. " ++ show f
        | otherwise = do
            let (rec, nonRec) = partition (\(x,_) -> x == TRec) (conArgs `zip` args)
            liftM2 (,) (traverse (safeFromVar . snd) rec) (traverse (safeFromVar . snd) nonRec)
        where
            safeFromVar (Variable v) = return v
            safeFromVar cyp = Left $ "Term '" ++ show cyp ++ "' used in induction is not a variable."


{- Pretty printing --------------------------------------------------}

printProp :: Prop -> String
printProp (Prop l r) = printInfo l ++ " = " ++ printInfo r

printInfo :: Cyp -> String
printInfo (Application cypCurry cyp) = "((" ++ (printInfo cypCurry) ++ ") " ++ (printInfo cyp) ++ ")"
printInfo (Literal a) = translateLiteral a
printInfo (Variable a) = "?" ++ a
printInfo (Const a) = a


{- Parse inner syntax -----------------------------------------------}

translate :: (String -> Either String Cyp) -> Exp -> Either String Cyp
translate f (Var v) = f $ translateQName v
translate _ (Con c) = Right $ Const $ translateQName c
translate _ (Lit l) = Right $ Literal l
translate f (InfixApp e1 op e2) =
    translateQOp f op `mApp` translate f e1 `mApp` translate f e2
translate f (App e1 e2) = translate f e1 `mApp` translate f e2
translate f (NegApp e) = return (Const "-") `mApp` translate f e
translate f (LeftSection e op) = translateQOp f op `mApp` translate f e
translate f (Paren e) = translate f e
translate f (List l) = foldr (\e es -> Right (Const ":") `mApp` translate f e `mApp` es) (Right $ Const "[]") l
translate _ e = Left $ "Unsupported expression syntax used: " ++ show e

translateQOp :: (String -> Either String Cyp) -> QOp -> Either String Cyp
translateQOp _ (QConOp op) = Right $ Const $ translateQName op
translateQOp f (QVarOp op) = f $ translateQName op


translateQName :: QName -> String
translateQName (Qual (ModuleName m) (Ident n)) = m ++ "." ++ n
translateQName (Qual (ModuleName m) (Symbol n)) = m ++ "." ++ n
translateQName (UnQual (Ident n)) = n
translateQName (UnQual (Symbol n)) = n
translateQName (Special UnitCon) = "()"
translateQName (Special ListCon) = "[]"
translateQName (Special FunCon) = "->"
translateQName (Special Cons) = ":"
translateQName _ = ""

translateLiteral :: Literal -> String
translateLiteral (Char c) = [c]
translateLiteral (String s) = s
translateLiteral (Int c) = show c
translateLiteral (Frac c) = show c
translateLiteral (PrimInt c) = show c
translateLiteral (PrimWord c) = show c
translateLiteral (PrimFloat c) = show c
translateLiteral (PrimDouble c) = show c
translateLiteral (PrimChar c) = [c]
translateLiteral (PrimString c) = c

stripComb :: Cyp -> (Cyp, [Cyp])
stripComb cyp = work (cyp, [])
  where work (Application f a, xs) = work (f, a : xs)
        work x = x

readDataType :: [ParseDeclTree] -> Either String [DataType]
readDataType = sequence . mapMaybe parseDataType
  where
    parseDataType (DataDecl s) = Just $ do
        (tycon : dacons) <- traverse parseCons $ splitStringAt "=|" s []
        tyname <- constName $ fst $ stripComb tycon
        dacons' <- traverse (parseDacon tycon) dacons
        return $ DataType tyname dacons'
    parseDataType _ = Nothing

    parseCons :: String -> Either String Cyp
    parseCons s = iparseExp baseParseMode s >>= translate (Right . Variable)

    constName (Const c) = return c
    constName cyp = Left $ "Term '" ++ show cyp ++ "' is not a constant."

    parseDacon tycon cyp = do
        let (con, args) = stripComb cyp
        name <- constName con
        args' <- traverse (parseDaconArg tycon) args
        return (name, args')

    parseDaconArg tycon cyp | cyp == tycon = return TRec
    parseDaconArg _ (Application _ _) = Left $ "Nested constructors (apart from direct recursion) are not allowed."
    parseDaconArg _ (Literal _) = Left $ "Literals not allowed in datatype declarations"
    parseDaconArg _ _ = return TNRec

readAxiom :: [String] -> [ParseDeclTree] -> Either String [Prop]
readAxiom consts = sequence . mapMaybe parseAxiom
  where
    parseAxiom (Axiom s) = Just $ iparseProp env s
    parseAxiom _ = Nothing

    env = Env { datatypes = [], constants = consts, axioms = [] }

readSym :: [ParseDeclTree] -> Either String [String]
readSym = sequence . mapMaybe parseSym
  where
    parseSym (SymDecl s) = Just $ do
        cyp <- iparseExp baseParseMode s >>= translate (Right . Const)
        case cyp of
            Const v -> Right v
            _ -> Left $ "Expression '" ++ s ++ "' is not a symbol"
    parseSym _ = Nothing


readFunc :: [String] -> [ParseDeclTree] -> Either String ([Prop], [String])
readFunc syms pds = do
    rawDecls <- sequence . mapMaybe parseFunc $ pds
    let syms' = syms ++ map (\(sym, _, _) -> sym) rawDecls
    props <- traverse (declToProp syms') rawDecls
    return (props, syms')
  where
    strOfName (Ident s) = s
    strOfName (Symbol s) = s

    listComb = foldl Application

    declToProp :: [String] -> (String, [Exts.Pat], Exts.Exp) -> Either String Prop
    declToProp consts (funSym, pats, rawRhs) = do
        tPat <- traverse translatePat pats
        rhs <- translate tv rawRhs
        return $ Prop (listComb (Const funSym) tPat) rhs
      where
        pvars = concatMap collectPVars pats
        tv s | s `elem` pvars = Right $ Variable s
             | s `elem` consts = Right $ Const s -- XXX Strange?
             | otherwise = Left $ "Unbound variable '" ++ s ++ "' not allowed on rhs"

    collectPVars :: Exts.Pat -> [String]
    collectPVars (Exts.PVar v) = [strOfName v]
    collectPVars (Exts.PInfixApp p1 _ p2) = collectPVars p1 ++ collectPVars p2
    collectPVars (Exts.PApp _ ps) = concatMap collectPVars ps
    collectPVars (Exts.PList ps) = concatMap collectPVars ps
    collectPVars (Exts.PParen p) = collectPVars p
    collectPVars _ = []

    translatePat :: Exts.Pat -> Either String Cyp
    translatePat (Exts.PVar v) = Right $ Variable $ strOfName v
    translatePat (Exts.PLit l) = Right $ Literal l
    -- PNeg?
    translatePat (Exts.PNPlusK _ _) = Left "n+k patterns are not supported"
    translatePat (Exts.PInfixApp p1 qn p2) =
        (Right $ Const $ translateQName qn) `mApp` translatePat p1 `mApp` translatePat p2
    translatePat (Exts.PApp qn ps) = do
        cs <- traverse translatePat ps
        return $ listComb (Const $ translateQName qn) cs
    translatePat (Exts.PTuple _) = Left "tuple patterns are not supported"
    translatePat (Exts.PList ps) = foldr (\p cs -> Right (Const ":") `mApp` translatePat p `mApp` cs) (Right $ Const "[]") ps
    translatePat (Exts.PParen p) = translatePat p
    translatePat (Exts.PAsPat _ _) = Left "as patterns are not supported"
    translatePat Exts.PWildCard = Left "wildcard patterns are not supported"
    translatePat f = Left $ "unsupported pattern type: " ++ show f

    parseFunc :: ParseDeclTree -> Maybe (Either String (String, [Exts.Pat], Exts.Exp))
    parseFunc (FunDef s) = Just $ case parseDecl s of
        ParseOk (Exts.FunBind [Exts.Match _ name pat _ (Exts.UnGuardedRhs rhs) (Exts.BDecls [])])
            -> Right (strOfName name, pat, rhs)
        ParseOk _ -> Left $ "Invalid function definition '" ++ s ++ "'."
        f@(ParseFailed _ _ ) -> Left $ show f
    parseFunc _ = Nothing

iparseExp :: ParseMode -> String -> Either String Exp
iparseExp mode s = case parseExpWithMode mode s of
    ParseOk p -> Right p
    f@(ParseFailed _ _) -> Left $ show f

iparseCypWithMode :: ParseMode -> Env -> String -> Either String Cyp
iparseCypWithMode mode env s = do
    p <- iparseExp mode s
    translate tv p
  where tv x = Right $ if x `elem` constants env then Const x else Variable x

iparseCyp :: Env -> String -> Either String Cyp
iparseCyp = iparseCypWithMode baseParseMode


iparseProp :: Env -> String -> Either String Prop
iparseProp env x = do
    cyp <- iparseCypWithMode mode env' x
    case cyp of
-- XXX: handle ".=." differently! -> Const; Exclude ".=." from inner terms ...
        Application (Application (Variable ".=.") lhs) rhs -> Right $ Prop lhs rhs
        _ -> Left $ "Term '" ++ x ++ "' is not a proposition"
  where
    env' = env { constants = ".=" : constants env }
    mode = baseParseMode { fixities = Just $ Fixity AssocNone (-1) (UnQual $ Symbol ".=.") : baseFixities }

splitStringAt :: Eq a => [a] -> [a] -> [a] -> [[a]]
splitStringAt _ [] h 
	| h == [] = []
	| otherwise = h : []
splitStringAt a (x:xs) h 
	| x `elem` a = h : splitStringAt a xs []
	| otherwise = splitStringAt a xs (h++[x])
												 

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace


{- Parser for the outer syntax --------------------------------------}

toParsec :: (a -> String) -> Either a b -> Parsec c u b
toParsec f = either (fail . f) return

eol :: Parsec [Char] u ()
eol = do
    _ <- try (string "\n\r") <|> try (string "\r\n") <|> string "\n" <|> string "\r"
        <?> "end of line"
    return ()

commentParser :: Parsec [Char] u ()
commentParser =
    do  _ <- string "--" 
        _ <- many (noneOf "\r\n")
        eol
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
       result <- (dataParser <|> axiomParser <|> symParser <|> try funParser)
       return result

axiomParser :: Parsec [Char] () ParseDeclTree
axiomParser =
    do  keyword "lemma" 
        result <- many1 (noneOf "\r\n")
        eol
        return (Axiom result)

dataParser :: Parsec [Char] () ParseDeclTree
dataParser =
    do  keyword "data"
        result <- many1 (noneOf "\r\n" )
        eol
        return (DataDecl result)

symParser :: Parsec [Char] () ParseDeclTree
symParser =
    do  keyword "declare_sym" 
        result <- trim <$> many1 (noneOf "\r\n")
        eol
        return (SymDecl result)

funParser :: Parsec [Char] () ParseDeclTree
funParser =
    do  result <- many1 (noneOf "\r\n")
        eol
        return (FunDef result)

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
        manySpacesOrComment
        over <- toEol
        manySpacesOrComment
        cases <- many1 caseParser
        manySpacesOrComment
        keywordQED
        return (ParseInduction datatype over cases)

propParser :: Parsec [Char] Env Prop
propParser = do
    text <- many (noneOf "\r\n")
    env <- getState
    toParsec (\err -> "Failed to parse expression: " ++ err) (iparseProp env text)

lemmaParser :: Parsec [Char] Env ParseLemma
lemmaParser =
    do  keyword "Lemma:"
        prop <- propParser
        eol
        manySpacesOrComment
        prf <- inductionProofParser <|> equationProofParser
        manySpacesOrComment
        return $ ParseLemma prop prf

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

toEol :: Parsec [Char] Env String
toEol = do
    res <- many1 (noneOf "\r\n")
    eol
    return res

equationsParser :: Parsec [Char] Env [Cyp]
equationsParser = do
    eq1 <- equations'
    eq2 <- option [] (try equations')
    return $ eq1 ++ reverse eq2
  where
    equations' = do
        spaces
        l <- toEol
        ls <- many1 (try (manySpacesOrComment >> string ".=." >> lineSpaces >> toEol))
        env <- getState
        let eqs = map (iparseCyp env) (l : ls)
        toParsec fmt . sequence $ eqs
    fmt err = "Failed to parse expression: " ++ err

caseParser :: Parsec [Char] Env (String, [Cyp])
caseParser = do
    keywordCase
    manySpacesOrComment
    cons <- trim <$> toEol
    manySpacesOrComment
    eqns <- equationsParser
    manySpacesOrComment
    return (cons, eqns)

manySpacesOrComment :: Parsec [Char] u ()
manySpacesOrComment = skipMany $ (space >> return ()) <|> commentParsers

-- Parse Mode with Fixities
baseParseMode :: ParseMode
baseParseMode = defaultParseMode { fixities = Just baseFixities }
