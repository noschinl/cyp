module CheckYourProof where
import Data.Char
import Control.Applicative ((<$>), (<*>))
import Control.Monad
import Data.List
import Data.Maybe
import Data.Foldable (traverse_)
import Data.Traversable (traverse)
import Text.Parsec as Parsec
import Text.Parsec.Combinator as Parsec
import Text.Parsec.Prim as Parsec
import Text.Parsec.Char as Parsec
import Text.Parsec.String as Parsec
import Language.Haskell.Exts.Parser 
import Language.Haskell.Exts.Fixity
import Language.Haskell.Exts.Extension
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
    | SymDecl String -- Symbol (, Arity)
    | Axiom String
    | FunDef String
    deriving Show

data ParseLemma = ParseLemma Prop ParseProof -- Proposition, Proof

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

data DataType = DataType String [(String, TCyp)] -- name cases
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

data TCyp = TApplication TCyp TCyp | TConst String | TNRec String | TRec
    deriving (Show, Eq)

tracePretty :: Show a => a -> b -> b
tracePretty = trace . ppShow

tracePrettyA :: Show a => a -> a
tracePrettyA x = tracePretty x x

tracePrettyF :: Show b => (a -> b) -> a -> a
tracePrettyF f x = tracePretty (f x) x

proof masterFile studentFile = do
    mContent <- readFile masterFile
    sContent <- readFile studentFile
    let env = do
        mResult <- showLeft $ Parsec.parse masterParser masterFile mContent
        dts <- readDataType mResult
        syms <- readSym mResult
        let (fundefs, consts) = readFunc mResult syms
        axioms <- readAxiom consts mResult
        return $ Env { datatypes = dts, axioms = fundefs ++ axioms , constants = consts }
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

checkProof :: Env -> ParseLemma -> Either String ()
checkProof env (ParseLemma prop (ParseEquation eqns)) = validEquationProof (axioms env) eqns prop
checkProof env (ParseLemma prop (ParseInduction dtRaw overRaw casesRaw)) = do
    dt <- validateDatatype env dtRaw
    over <- validateOver env overRaw
    cases <- validateCases env dt casesRaw
    traverse_ (check dt over) cases
  where
    check sdt over cas = case makeProof prop (snd cas) over sdt (axioms env) of
        Right x -> Right x
        Left x -> Left $ "Error in case '" ++ (fst cas) ++ "' " ++ x

    validateDatatype env name = case find (\dt -> getDtName dt == name) (datatypes env) of
        Nothing -> Left $  "Invalid datatype '" ++ name ++ "'. Expected one of "
            ++ show (map getDtName $ datatypes env)
        Just dt -> Right dt

    validateOver env text = do
        exp <- iparseExp baseParseMode text
        case translate exp [] [] true of -- XXX: We should take the constant list into account?
            Variable v -> return v
            _ -> Left $ "Variable '" ++ text ++ "' is not a valid induction variable"

    validateCases env dt cases = do
        case missingCase of
            Nothing -> return cases
            Just (name, _) -> Left $ "Missing case '" ++ name ++ "'"
        case invalidCase of
            Nothing -> return cases
            Just name -> Left $ "Invalid case '" ++ name ++ "'"
      where
        conss = getDtConss dt
        caseNames = map fst cases
        missingCase = find (\(name, _) -> name `notElem` caseNames) conss
        invalidCase = find (\name -> all (\cons -> fst cons /= name ) conss) caseNames

    getDtConss (DataType _ conss) = conss
    getDtName (DataType n _) = n


listOfProp :: Prop -> [Cyp]
listOfProp (Prop l r) = [l, r]

makeProof :: Prop -> [Cyp] -> String -> DataType -> [Prop] -> Either String ()
makeProof prop step over (DataType name datatype) rules = proof
    where
        prop' = listOfProp prop
        rules' = map listOfProp rules
        (newlemma, _, laststep, static) = mapFirstStep prop' step over datatype
        -- XXX: get rid of makeSteps
        proof = makeSteps (rules' ++ newlemma) (map (\x -> transformVartoConstList x static elem) step) 
            (transformVartoConstList laststep static elem)

validEquations :: [Prop] -> [Cyp] -> Either String ()
validEquations _ [] = Left "Empty equation sequence"
validEquations _ [_] = Right ()
validEquations rules (t1:t2:ts)
    | t2 `elem` applyall t1 (map listOfProp rules) = validEquations rules (t2:ts)
    | otherwise = Left $ "(nmr) No matching rule: step " ++ printInfo t1 ++ " to " ++ printInfo t2

validEquationProof :: [Prop] -> [Cyp] -> Prop -> Either String ()
validEquationProof rules eqns aim = do
    validEquations rules eqns
    let proved = Prop (head eqns) (last eqns)
    if proved == aim
        then Right ()
        else Left ("Proved proposition does not match goal:\n" ++ printProp proved ++ "\nvs.\n" ++ printProp aim)



makeSteps :: [[Cyp]] -> [Cyp] -> Cyp -> Either String ()
makeSteps rules (x:y:steps) aim 
    | y `elem` applyall x rules = makeSteps rules (y:steps) aim
    | otherwise = Left $ "(nmr) No matching rule: step " ++ printInfo x ++ " to " ++ printInfo  y
makeSteps rules [x] aim 
    | x == aim = Right ()
    | x /= aim = Left $ "(eop) End of proof is not the right side of induction: " ++ printInfo x ++ " to " ++ printInfo aim
makeSteps _ _ _ = Left $ "Error"

applyall :: Cyp -> [[Cyp]] -> [Cyp]
applyall step rules = concatMap (\rule -> concat $ nub [apply step (x, y) | x <- rule, y <- rule]) rules

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

apply_top :: Cyp -> (Cyp,Cyp) -> Maybe Cyp
apply_top t (lhs, rhs) = fmap (subst rhs) $ match t lhs []

apply :: Cyp -> (Cyp,Cyp) -> [Cyp]
apply t@(Application f a) eq =
    maybeToList (apply_top t eq)
    ++ map (\x -> Application x a) (apply f eq)
    ++ map (Application f) (apply a eq)
apply t eq = maybeToList $ apply_top t eq

edit :: Cyp -> [(Cyp, Cyp)] -> Cyp
edit (Application cypcurry cyp) x = Application (edit cypcurry x) (edit cyp x)
edit (Const a) _ = (Const a)
edit (Literal a) _ = (Literal a)
edit (Variable a) x = extract (lookup (Variable a) x)
	where
		extract (Just n) = n
		extract (Nothing) = (Variable a)
		
printCypEquoations :: [[Cyp]] -> [[String]]
printCypEquoations [] = []
printCypEquoations (x:xs) = [map printInfo x] ++ (printCypEquoations xs)

printRunnable :: Cyp -> String
printRunnable (Application cypCurry cyp) = "(" ++ (printRunnable cypCurry) ++ " " ++ (printRunnable cyp) ++ ")"
printRunnable (Literal a) = translateLiteral a
printRunnable (Variable a) = a
printRunnable (Const a) = a

printProp :: Prop -> String
printProp (Prop l r) = printInfo l ++ " = " ++ printInfo r

printInfo :: Cyp -> String
printInfo (Application cypCurry cyp) = "((" ++ (printInfo cypCurry) ++ ") " ++ (printInfo cyp) ++ ")"
printInfo (Literal a) = translateLiteral a
printInfo (Variable a) = "?" ++ a
printInfo (Const a) = a

getGoals :: [TCyp] -> TCyp -> [(String, TCyp)]
getGoals xs goal = map (\x -> (getConstructorName x, getGoal x goal)) xs

getGoal :: TCyp -> TCyp -> TCyp
getGoal maybeGoal@(TApplication cypCurry cyp) goal
    | maybeGoal == goal = TRec
    | otherwise = TApplication (getGoal cypCurry goal) (getGoal cyp goal)
getGoal (TNRec a) goal = TNRec a
getGoal maybeGoal@(TConst a) goal
    | maybeGoal == goal = TRec
    | otherwise = TConst a

translateToTyp :: Cyp -> TCyp
translateToTyp (Application cypcurry cyp) = TApplication (translateToTyp cypcurry) (translateToTyp cyp)
translateToTyp (Variable a) = TNRec a
translateToTyp (Const a) = TConst a

getConstructorName :: TCyp -> String
getConstructorName (TApplication (TConst a) cyp) = a
getConstructorName (TConst a) = a
getConstructorName (TApplication cypCurry cyp) = getConstructorName cypCurry

strip_comb :: Exp -> (ConstList, VariableList)
strip_comb x = strip_comb' x True
    where
        strip_comb' :: Exp -> Bool -> (ConstList, VariableList)
        strip_comb' (Var n) True = ([translateQName n], [])
        strip_comb' (Var n) False = ([], [translateQName n])
        strip_comb' (Con c) _ = ([translateQName c], [])
        strip_comb' (App e1 e2) b = (cs1 ++ cs2, vs1 ++ vs2)
            where
                (cs1,vs1) = strip_comb' e1 b
                (cs2,vs2) = strip_comb' e2 False
        strip_comb' (InfixApp e1 (QConOp i) e2) b = ([translateQName i] ++ cs1 ++ cs2 , vs1 ++ vs2)
            where
                (cs1,vs1) = strip_comb' e1 b
                (cs2,vs2) = strip_comb' e2 False
        strip_comb' (InfixApp e1 (QVarOp i) e2) b = ([translateQName i] ++ cs1 ++ cs2, vs1 ++ vs2)
            where
                (cs1,vs1) = strip_comb' e1 b
                (cs2,vs2) = strip_comb' e2 False
        strip_comb' (Paren e) b = strip_comb' e b
        strip_comb' (List []) _ = (["[]"], [])
        strip_comb' (List (x:xs)) _ = ([":"] ++ csh ++ cst, vsh ++ vst)
            where
                (csh,vsh) = strip_comb' x False
                (cst,vst) = strip_comb' (List xs) False

getConstList :: (ConstList, VariableList) -> ConstList
getConstList (cons ,_) = cons

getVariableList :: (ConstList, VariableList) -> VariableList
getVariableList (_, var) = var

translate :: Exp -> ConstList -> VariableList -> (String -> [String] -> Bool)-> Cyp
translate (Var v) cl vl f
    | elem (translateQName v) cl = Const (translateQName v)
    | f (translateQName v) vl = Variable (translateQName v)
translate (Con c) cl vl f = Const (translateQName c)
translate (Lit l) cl vl f = Literal l
translate (InfixApp e1 (QConOp i) e2) cl vl f 
    = Application (Application (Const (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
translate (InfixApp e1 (QVarOp i) e2) cl vl f
    | elem (translateQName i) cl =  Application (Application (Const (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
    | f (translateQName i) vl =  Application (Application (Variable (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
translate (App e1 e2)  cl vl f = Application (translate e1 cl vl f) (translate e2 cl vl f)
translate (Paren e) cl vl f = translate e cl vl f
translate (List l) cl vl f
    | null(l) = Const ("[]")
    | otherwise = Application (Application (Const (":")) (translate (head l) cl vl f)) (translate (List (tail l)) cl vl f)

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

true :: a -> b -> Bool
true _ _ = True

mapFirstStep :: [Cyp] -> [Cyp] -> String -> [(String, TCyp)] -> ([[Cyp]], [Cyp], Cyp, [Cyp])
mapFirstStep prop firststeps over goals =
    ( map (\x -> map (\y -> createNewLemmata y over x) prop) (concat fmg)
    , concat fmg
    , head lastStep
    , concat tmg
    )
    where
        lastStep = parseLastStep (head $ prop) (head $ firststeps) over (last $ prop)
        (fmg, _ , tmg) = unzip3 mapGoals
            where
                mapGoals = concatMap (\z -> map (\(y,x) -> goalLookup x z over (y,x)) goals) 
                    (parseFirstStep (head $ prop) (head $ firststeps) over)

parseFirstStep :: Cyp -> Cyp -> String -> [Cyp]
parseFirstStep (Variable n) m over
	| over == n =  [m]
    | otherwise = []
parseFirstStep (Literal l) _ _ = []
parseFirstStep (Const c) _ _  = []
parseFirstStep (Application cypCurry cyp) (Application cypthesisCurry cypthesis) over 
    = (parseFirstStep cypCurry cypthesisCurry over) ++ (parseFirstStep cyp cypthesis over)
parseFirstStep _ _ _ = []

goalLookup :: TCyp -> Cyp -> String -> (String, TCyp) -> ([Cyp], [(String, TCyp)], [Cyp])
goalLookup (TApplication tcypcurry tcyp) (Application cypcurry cyp) over x 
	| length  (sgl ++ scgl) == 0 = (fgl ++ fcgl, sgl ++ scgl, tgl ++ tcgl)
	| otherwise = ([], [], [])
	where
		(fgl, sgl, tgl) = goalLookup tcyp cyp over x
		(fcgl, scgl, tcgl) = goalLookup tcypcurry cypcurry over x
goalLookup (TConst a) (Const b) over x 
	| a == b = ([], [], [])
	| otherwise = ([], [x], [])
goalLookup (TNRec a) (Variable b) _ _ = ([], [], [Variable b])
goalLookup (TRec) b over x = ([b], [], [b])
goalLookup _ _ _  x = ([], [x], [])

parseLastStep :: Cyp -> Cyp -> String -> Cyp -> [Cyp]
parseLastStep (Variable n) m over last
	| over == n =  [edit last [(Variable n, m)]]
    | otherwise = []
parseLastStep (Literal l) _ _ _ = []
parseLastStep (Const c) _ _ _ = []
parseLastStep (Application cypCurry cyp) (Application cypthesisCurry cypthesis) over last 
    = (parseLastStep cypCurry cypthesisCurry over last) ++ (parseLastStep cyp cypthesis over last)
parseLastStep _ _ _ _ = []


createNewLemmata :: Cyp -> String -> Cyp -> Cyp
createNewLemmata (Application cypcurry cyp) over b =  Application (createNewLemmata cypcurry over b) (createNewLemmata cyp over b)
createNewLemmata (Variable a) over (Const b) 
	| over == a = Const b
	| otherwise = Variable a
createNewLemmata (Variable a) over (Variable b) 
	| over == a = Const b
	| otherwise = Variable a
createNewLemmata (Const a) over (Const b) 
	| over == a = Const b
	| otherwise = Const a
createNewLemmata (Const a) over (Variable b) 
	| over == a = Const b
	| otherwise = Const a
createNewLemmata (Literal a) _ _ = Literal a

transformVartoConst :: Cyp -> Cyp
transformVartoConst x = transformVartoConstList x [] true

transformVartoConstList :: Cyp -> [Cyp] -> (Cyp -> [Cyp] -> Bool) -> Cyp
transformVartoConstList (Variable v) list f | f (Variable v) list = Const v
                                            | otherwise = Variable v
transformVartoConstList (Const v) _ _ = Const v
transformVartoConstList (Application cypCurry cyp) list f 
    = Application (transformVartoConstList cypCurry list f) (transformVartoConstList cyp list f)
transformVartoConstList (Literal a) _ _ = Literal a

readDataType :: [ParseDeclTree] -> Either String [DataType]
readDataType = sequence . mapMaybe parseDecl
  where
    parseDecl (DataDecl s) = Just $ do
        (tycon : dacons) <- traverse parseCons $ splitStringAt "=|" (trimh s) [] -- XXX: trimh necessary?
        return $ DataType (getConstructorName tycon) (getGoals dacons tycon)
    parseDecl _ = Nothing

    parseCons :: String -> Either String TCyp
    parseCons s = do
        exp <- iparseExp baseParseMode s
        return $ translateToTyp $ translate exp [] [] true


readAxiom :: [String] -> [ParseDeclTree] -> Either String [Prop]
readAxiom consts = sequence . mapMaybe parseAxiom
  where
    parseAxiom (Axiom s) = Just $ iparseProp env $ trimh s -- XXX: trimh needed?
    parseAxiom _ = Nothing

    env = Env { datatypes = [], constants = consts, axioms = [] }

readSym :: [ParseDeclTree] -> Either String [Cyp]
readSym = sequence . mapMaybe parseSym
  where
    parseSym (SymDecl s) = Just $ do
        exp <- iparseExp baseParseMode s
        return $ transformVartoConst $ translate exp [] [] true
    parseSym _ = Nothing

-- XXX: readFunc should probably use parseDecl!
readFunc :: [ParseDeclTree] -> [Cyp] -> ([Prop], [String])
readFunc pr sym =
        ( zipWith (parseFunc symConsts) pr' ipl
        , nub $ concatMap getConstList ipl ++ symConsts
        )
    where
        pr' = mapMaybe (\x -> case x of { FunDef s -> Just $ trimh s; _ -> Nothing }) pr
        ipl = map innerParseList pr'
        symConsts = nub $ mapMaybe (\x -> case x of { Const y -> Just y; _ -> Nothing}) sym

        parseFunc :: [String] -> String -> (ConstList, VariableList) -> Prop
        parseFunc consts r l = Prop (innerParseFunc consts head r l) (innerParseFunc consts last r l)

        innerParseFunc :: [String] -> ([String] -> String) -> String -> (ConstList, VariableList) -> Cyp
        innerParseFunc consts f s v = parseDef (f $ splitStringAt "=" s []) (consts ++ getConstList v) (getVariableList v)
          where parseDef s g v = translate (transform $ parseExpWithMode baseParseMode s) g v elem

        innerParseList :: String -> (ConstList, VariableList)
        innerParseList x = parseLists $ head (splitStringAt "=" x [])

        parseLists :: String -> (ConstList, VariableList)
        parseLists x = strip_comb $ transform $ parseExpWithMode baseParseMode  x

iparseExp :: ParseMode -> String -> Either String Exp
iparseExp mode s = case parseExpWithMode mode s of
    ParseOk p -> Right p
    f@(ParseFailed _ _) -> Left $ show f

iparseCypWithMode :: ParseMode -> Env -> String -> Either String Cyp
iparseCypWithMode mode env s = do
    p <- iparseExp mode s
    return $ translate p (constants env) [] true

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


transform :: ParseResult t -> t
transform (ParseOk a) = a
    	
deleteAll :: Eq a => [a] -> (a->Bool) -> [a]
deleteAll [] _ = []
deleteAll (x:xs) a 
	| a x = deleteAll xs a
	| otherwise = x : (deleteAll xs a)
									 
splitStringAt :: Eq a => [a] -> [a] -> [a] -> [[a]]
splitStringAt a [] h 
	| h == [] = []
	| otherwise = h : []
splitStringAt a (x:xs) h 
	| x `elem` a = h : splitStringAt a xs []
	| otherwise = splitStringAt a xs (h++[x])
												 

trimh :: String -> String
trimh = reverse . dropWhile isSpace . reverse . dropWhile isSpace

trim :: [String] -> [String]
trim = map trimh

replace :: Eq a => [a] -> [a] -> [a] -> [a]
replace _ _ [] = []
replace old new (x:xs) 
	| isPrefixOf old (x:xs) = new ++ drop (length old) (x:xs)
	| otherwise = x : replace old new xs

toParsec :: (a -> String) -> Either a b -> Parsec c u b
toParsec f = either (fail . f) return

eol =   try (string "\n\r")
    <|> try (string "\r\n")
    <|> string "\n"
    <|> string "\r"
    <?> "end of line"

commentParser :: Parsec [Char] u ()
commentParser =
    do  string "--" 
        result <- many (noneOf "\r\n")
        eol
        return ()
longcommentParser :: Parsec [Char] u ()
longcommentParser =
    do  string "{-"
        result <- manyTill anyChar (try (string "-}"))
        return ()

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
        result <- trimh <$> many1 (noneOf "\r\n")
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
        env <- getState
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
        proof <- inductionProofParser <|> equationProofParser
        manySpacesOrComment
        return $ ParseLemma prop proof

studentParser ::  Parsec [Char] Env [ParseLemma]
studentParser =
    do  lemmas <- many1 lemmaParser
        eof
        return lemmas

lineSpaces = skipMany (oneOf " \t") <?> "horizontal white space"

keyword :: String -> Parsec [Char] u ()
keyword kw = try $ do
    string kw
    notFollowedBy alphaNum
    lineSpaces

keywordCase = keyword "Case"
keywordQED = keyword "QED"

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
        line <- toEol
        lines <- many1 (try (manySpacesOrComment >> string ".=." >> lineSpaces >> toEol))
        env <- getState
        let eqs = map (iparseCyp env) (line : lines)
        toParsec fmt . sequence $ eqs
    fmt err = "Failed to parse expression: " ++ err

caseParser :: Parsec [Char] Env (String, [Cyp])
caseParser = do
    keywordCase
    manySpacesOrComment
    cons <- trimh <$> toEol
    manySpacesOrComment
    eqns <- equationsParser
    manySpacesOrComment
    return (cons, eqns)
  where validCons (DataType _ conss) cons = any (\(name,_) -> name == cons) conss

manySpacesOrComment :: Parsec [Char] u ()
manySpacesOrComment = skipMany $ (space >> return ()) <|> commentParsers

-- Parse Mode with Fixities
baseParseMode = defaultParseMode { fixities = Just baseFixities }
