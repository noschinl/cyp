module CheckYourProof where
import Data.Char
import Control.Monad
--import Text.Regex
import Data.List
import Data.Maybe
import Text.Parsec
import Text.Parsec.Combinator
import Text.Parsec.Prim
import Text.Parsec.Char
import Text.Parsec.String
import Language.Haskell.Exts.Parser 
import Language.Haskell.Exts.Syntax(Literal (..), QName(..), SpecialCon (..), Name (..), ModuleName (..), Exp (..), QOp (..))

import Debug.Trace
import Text.Show.Pretty (ppShow)

{-
Copyright by Dominik Durner / Technische Universität München - Institute for Informatics - Chair for Logic and Verification (I21)

Check Your Proof (CYP)
 What is CYP?
 Check your Proof is a functional program for students to check the correctness of their proofs by induction over simple data structures (e.g. List, Trees)
	noschinl = Wiweni64
-}

type ConstList = [String]
type VariableList = [String]

data ParseTree
    = DataDecl String
    | SymDecl String -- Symbol (, Arity)
    | Axiom String
    | FunDef String
    | ParseLemma String ParseProof -- Proposition, Proof
    deriving Show

data ParseProof
    = ParseInduction String [(String, ParseEquations)] -- Over, Cases
    | ParseEquation ParseEquations
    deriving Show

type ParseEquations = [String]

data Prop = Prop Cyp Cyp -- lhs, rhs

data Proof
    = Induction String [(String, [Cyp])] -- ind var, ...
    -- XXX Induction must contain the datatype of the variable we do induction over
    | Equation [Cyp]

data Lemma = Lemma Prop Proof -- Proposition (_ = _), Proof


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

-- proof masterFile studentFile = do
--     masterContent <- readFile masterFile
--     parseDecls <- parseMaster masterContent
-- 
--     datatype <- readDataType parseDecls
--     sym <- varToConst $ readSym parseDecls
--     (func, globalConstList, new) <- readFunc parseDecls sym
--     let func' = map (\[x,y] -> Prop x y) func
--     axioms <- readAxiom parseDecls globalConstList

proof masterFile studentFile = do
    parseresult <- parsing masterFile studentFile

    datatype <- {-tracePretty parseresult $-} readDataType parseresult
    sym <- varToConst $ readSym parseresult
    (func, globalConstList, new) <- readFunc parseresult sym
    let func' = map (\[x,y] -> Prop x y) func
    axioms <- readAxiom parseresult globalConstList

    let lemmas = readLemmas parseresult globalConstList datatype -- lemmas -change name?
    let proof = checkProofs (func' ++ axioms) lemmas datatype
    return proof

checkProofs :: [Prop] -> [Lemma] -> [(String, TCyp)] -> [[String]]
checkProofs axs [] dt  = []
checkProofs axs (l@(Lemma prop _) : ls) dt = checkProof axs l dt : checkProofs (prop : axs) ls dt

checkProof :: [Prop] -> Lemma -> [(String, TCyp)] -> [String]
checkProof axs (Lemma prop (Equation _)) dt = undefined
checkProof axs (Lemma prop (Induction over cases)) dt =
    map (\x -> makeProof prop x over dt axs) (map snd cases)

listOfProp :: Prop -> [Cyp]
listOfProp (Prop l r) = [l, r]

makeProof :: Prop -> [Cyp] -> String -> [(String, TCyp)] -> [Prop] -> String
makeProof prop step over datatype rules = proof
    where
        prop' = listOfProp prop -- XXX
        rules' = map listOfProp rules -- XXX
        (newlemma, _, laststep, static) = mapFirstStep prop' step over datatype
        proof = makeSteps (rules' ++ newlemma) (map (\x -> transformVartoConstList x static elem) step) (transformVartoConstList laststep static elem)

makeSteps rules (x:y:steps) aim 
    | y `elem` applyall x rules = makeSteps rules (y:steps) aim
    | otherwise = "Error - (nmr) No matching rule: step " ++ printInfo x ++ " to " ++ printInfo  y
makeSteps rules [x] aim 
    | x == aim = []
    | x /= aim = "Error - (eop) End of proof is not the right side of induction: " ++ printInfo x ++ " to " ++ printInfo aim
makeSteps _ _ _ = "Error"

applyall step rules = concatMap (\rule -> concat $ nub [apply step (x, y) | x <- rule, y <- rule]) rules


match :: Cyp -> Cyp -> Maybe [(String, Cyp)]
match term pat = match' term pat []
    where
        match' (Application f a) (Application f' a') s = match' f f' s >>= match' a a'
        match' (Literal a) (Literal b) s
            | a == b = Just s
            | otherwise = Nothing
        match' (Const a) (Const b) s
            | a == b = Just s
            | otherwise = Nothing
        match' t (Variable v) s = case lookup v s of
            Nothing -> Just $ (v,t) : s
            Just t' -> if t == t' then Just s else Nothing
        match' _ _ _ = Nothing

subst :: Cyp -> [(String, Cyp)] -> Cyp
subst (Application f a) s = Application (subst f s) (subst a s)
subst (Variable v) s = case lookup v s of
      Nothing -> Variable v
      Just t -> t
subst t _ = t

apply_top :: Cyp -> (Cyp,Cyp) -> Maybe Cyp
apply_top t (lhs, rhs) = fmap (subst rhs) $ match t lhs

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
	
printCypEquoations [] = []
printCypEquoations (x:xs) = [map printInfo x] ++ (printCypEquoations xs)

printRunnable :: Cyp -> String
printRunnable (Application cypCurry cyp) = "(" ++ (printRunnable cypCurry) ++ " " ++ (printRunnable cyp) ++ ")"
printRunnable (Literal a) = translateLiteral a
printRunnable (Variable a) = a
printRunnable (Const a) = a

printInfo :: Cyp -> String
printInfo (Application cypCurry cyp) = "(" ++ (printInfo cypCurry) ++ " " ++ (printInfo cyp) ++ ")"
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

translateToTyp (Application cypcurry cyp) = TApplication (translateToTyp cypcurry) (translateToTyp cyp)
translateToTyp (Variable a) = TNRec a
translateToTyp (Const a) = TConst a

getConstructorName (TApplication (TConst a) cyp) = a
getConstructorName (TConst a) = a
getConstructorName (TApplication cypCurry cyp) = getConstructorName cypCurry

getLists :: Exp -> (ConstList, VariableList)
getLists (Var v) = ([], [translateQName v])
getLists (Con c) = ([translateQName c], [])
getLists (Lit l) = ([], [])
getLists (InfixApp e1 (QConOp i) e2) = (cs1 ++ cs2 ++ [translateQName i], vs1 ++ vs2)
    where
        (cs1,vs1) = getLists e1
        (cs2,vs2) = getLists e2
getLists (InfixApp e1 (QVarOp i) e2) = (cs1 ++ cs2 ++ [translateQName i], vs1 ++ vs2)
    where
        (cs1,vs1) = getLists e1
        (cs2,vs2) = getLists e2
{- ganz wichtig für die Erkennung des Namens einer linken Seite der Func Def als Const -}
getLists (App (Var i) e) = ((translateQName i):cs, vs)
    where
        (cs,vs) = getLists e
getLists (App e1 e2) = (cs1 ++ cs2, vs1 ++ vs2)
    where
        (cs1,vs1) = getLists e1
        (cs2,vs2) = getLists e2
getLists (Paren e) = getLists e
getLists (List []) = (["[]"], [])
getLists (List (x:xs)) = (csh ++ cst ++ [":"], vsh ++ vst)
    where
        (csh,vsh) = getLists x
        (cst,vst) = getLists (List xs)

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
translate (InfixApp e1 (QConOp i) e2) cl vl f = Application (Application (Const (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
translate (InfixApp e1 (QVarOp i) e2) cl vl f
    | elem (translateQName i) cl =  Application (Application (Const (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
    | f (translateQName i) vl =  Application (Application (Variable (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
translate (App e1 e2)  cl vl f = Application (translate e1 cl vl f) (translate e2 cl vl f)
translate (Paren e) cl vl f = translate e cl vl f
translate (List l) cl vl f
    | null(l) = Const ("[]")
    | otherwise = Application (Application (Const (":")) (translate (head l) cl vl f)) (translate (List (tail l)) cl vl f)

translateQName (Qual (ModuleName m) (Ident n)) = m ++ "." ++ n
translateQName (Qual (ModuleName m) (Symbol n)) = m ++ "." ++ n
translateQName (UnQual (Ident n)) = n
translateQName (UnQual (Symbol n)) = n
translateQName (Special UnitCon) = "()"
translateQName (Special ListCon) = "[]"
translateQName (Special FunCon) = "->"
translateQName (Special Cons) = ":"
translateQName _ = ""

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
                mapGoals = concatMap (\z -> map (\(y,x) -> goalLookup x z over (y,x)) goals) (parseFirstStep (head $ prop) (head $ firststeps) over)

parseFirstStep :: Cyp -> Cyp -> String -> [Cyp]
parseFirstStep (Variable n) m over
	| over == n =  [m]
    | otherwise = []
parseFirstStep (Literal l) _ _ = []
parseFirstStep (Const c) _ _  = []
parseFirstStep (Application cypCurry cyp) (Application cypthesisCurry cypthesis) over = (parseFirstStep cypCurry cypthesisCurry over) ++ (parseFirstStep cyp cypthesis over)
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
parseLastStep (Application cypCurry cyp) (Application cypthesisCurry cypthesis) over last = (parseLastStep cypCurry cypthesisCurry over last) ++ (parseLastStep cyp cypthesis over last)
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

varToConst xs =
  do 
    cyp <- xs
    return (concatMap (map transformVartoConst) cyp)

transformVartoConst :: Cyp -> Cyp
transformVartoConst x = transformVartoConstList x [] true

transformVartoConstList :: Cyp -> [Cyp] -> (Cyp -> [Cyp] -> Bool) -> Cyp
transformVartoConstList (Variable v) list f | f (Variable v) list = Const v
                                            | otherwise = Variable v
transformVartoConstList (Const v) _ _ = Const v
transformVartoConstList (Application cypCurry cyp) list f = Application (transformVartoConstList cypCurry list f) (transformVartoConstList cyp list f)
transformVartoConstList (Literal a) _ _ = Literal a

readDataType pr = 
	do
		return (getGoals (tail $ head $ (innerParseDataType (tin pr))) (head $ head $ (innerParseDataType (tin pr))))
	where
		tin pr = trim $ inner pr
			where
				inner ((DataDecl p):pr) = p:(inner pr)
				inner (x:pr) = inner pr
				inner _ = []

readAxiom pr global = 
	do
		return (innerParseCyps (tin pr) global)
	where
		tin pr = trim $ inner pr
			where		
				inner ((Axiom p):pr) = p:(inner pr)
				inner (x:pr) = inner pr
				inner _ = []

readSym pr = 
	do
		return (innerParseSym (tin pr))
	where
		tin pr = trim $ inner pr
			where		
				inner ((SymDecl p):pr) = p:(inner pr)
				inner (x:pr) = inner pr
				inner _ = []

readFunc :: Monad m => [ParseTree] -> [Cyp] -> m ([[Cyp]], [String], [(ConstList, VariableList)])
readFunc pr sym = 
	do
		return (parseFunc (tin pr) (innerParseLists (tin pr)) (nub $ globalConstList [] sym), nub $ globalConstList (innerParseLists (tin pr)) sym, (innerParseLists (tin pr)))
	where
		tin pr = trim $ inner pr
			where
			inner ((FunDef p):pr) = p:(inner pr)
			inner (x:pr) = inner pr
			inner _ = []

readLemmas pr global dt = mapMaybe readLemma pr
    where
        readLemma (ParseLemma prop proof) = Just (Lemma prop' proof')
            where
                prop' = innerParseCyp (trimh prop) global
                proof' = readProof proof
        readLemma _ = Nothing

        readProof (ParseInduction over cases) = Induction over' cases'
            where
                -- XXX: list unnecessary? Parsing awkward ...
                over' = head $ getVariableList $ innerParseList $ over
                cases' = map (readCase cases) dt
        readProof (ParseEquation eqns) = Equation $ parseCyps eqns global

        -- XXX do not silently drop invalid cases!
        readCase cases dtcons = (fst cas, parseCyps (snd cas) global)
            where
                dtcons' = trimh $ fst dtcons -- XXX: Unnecessary?
                cas = case filter (\(name,eqns) -> trimh name == dtcons') cases of
                    [] -> undefined -- XXX error message
                    (x:_) -> x

globalConstList (x:xs) ys = getConstList x ++ (globalConstList xs ys)
globalConstList [] ((Const y):ys) = y : (globalConstList [] ys)
globalConstList [] [] = []

parseFunc r l g = zipWith (\a b -> [a, b]) (innerParseFunc r g l head) (innerParseFunc r g l last)

innerParseFunc [] _ _ _ = []
innerParseFunc (x:xs) g (v:vs) f = (parseDef (f (splitStringAt "=" x [])) (g ++ getConstList v) (getVariableList v)):(innerParseFunc xs g vs f)
  where
    parseDef x g v = translate (transform $ parseExp x) g v elem

innerParseList x = parseLists $ head (splitStringAt "=" x [])
innerParseLists = map innerParseList

parseLists x = getLists $ transform $ parseExp x

innerParseCyp pr global = Prop lhs rhs
    where [lhs, rhs] = parseCyps (splitStringAt "=" pr []) global
innerParseCyps prs global = map (\pr -> innerParseCyp pr global) prs

parseCyp x global = translate (transform $ parseExp x) global [] true
parseCyps xs global = map (\x -> parseCyp x global) xs

innerParseSym [] = []
innerParseSym (x:xs) = parseSym (splitStringAt "=" x []):(innerParseSym xs)

parseSym [] = []
parseSym (x:xs) = (translate (transform $ parseExp x) [] [] true)  : (parseSym xs)

innerParseDataType [] = []
innerParseDataType (x:xs) = parseDataType (splitStringAt "=|" x []):(innerParseDataType xs)

parseDataType [] = []
parseDataType (x:xs) = (translateToTyp (translate (transform $ parseExp x) [] [] true))  : (parseDataType xs)

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

replace _ _ [] = []
replace old new (x:xs) 
	| isPrefixOf old (x:xs) = new ++ drop (length old) (x:xs)
	| otherwise = x : replace old new xs

parsing :: String -> String -> IO [ParseTree]
parsing masterFile studentFile =
	do
		masterContent <- readFile masterFile
		studentContent <- readFile studentFile
		result <- returnParsing (parseMaster masterContent) (parseStudent studentContent)
		return $ removeEmptyFun result

removeEmptyFun ((FunDef x):xs)
	| length (splitStringAt "=" x []) > 0 = (FunDef x) : removeEmptyFun xs
	| otherwise = removeEmptyFun xs
removeEmptyFun (x:xs) = x:removeEmptyFun xs
removeEmptyFun [] = []
		
returnParsing (Left a) _ = 
    do
        putStr $ show a
        return []
returnParsing _  (Left a) = 
    do
        putStr $ show a
        return []
returnParsing (Right a) (Right b) = 
    do
        return (a++b)

parseMaster input = Text.Parsec.Prim.parse masterFile "(master)" input
parseStudent input = Text.Parsec.Prim.parse studentParser "(student)" input

eol =   try (string "\n\r")
    <|> try (string "\r\n")
    <|> string "\n"
    <|> string "\r"
    <?> "end of line"

commentParser :: Parsec [Char] () ()
commentParser =
    do  string "--" 
        result <- many (noneOf "\r\n")
        eol
        return ()
longcommentParser :: Parsec [Char] () ()
longcommentParser =
    do  string "{-"
        result <- manyTill anyChar (try (string "-}"))
        return ()

commentParsers =
    do 
        commentParser <|> longcommentParser
        return ()

masterFile :: Parsec [Char] () [ParseTree]
masterFile = 
    do result <- many masterParsers
       eof
       return result

masterParsers :: Parsec [Char] () ParseTree
masterParsers =
    do many space
       optionMaybe (try commentParser <|> try longcommentParser)
       result <- (try dataParser <|> try axiomParser <|> try symParser <|> funParser)
       return result

axiomParser :: Parsec [Char] () ParseTree
axiomParser =
    do  keyword "lemma" 
        result <- many (noneOf "\r\n")
        eol
        return (Axiom result)

dataParser :: Parsec [Char] () ParseTree
dataParser =
    do  keyword "data"
        result <- many (noneOf "\r\n" )
        eol
        return (DataDecl result)

symParser :: Parsec [Char] () ParseTree
symParser =
    do  keyword "declare_sym" 
        result <- many (noneOf "\r\n")
        eol
        return (SymDecl result)

funParser :: Parsec [Char] () ParseTree
funParser =
    do  result <- many (noneOf "\r\n")
        eol
        return (FunDef result)

equationProofParser :: Parsec [Char] () ParseProof
equationProofParser = do
    string "XXXXXX" -- XXX
    return $ ParseEquation []

inductionProofParser :: Parsec [Char] () ParseProof
inductionProofParser = 
    do  keyword "Proof by induction on"
        over <- many (noneOf "\r\n")
        eol
        manySpacesOrComment
        cases <- many1 caseParser
        manySpacesOrComment
        keywordQED
        return (ParseInduction over cases)

lemmaParser :: Parsec [Char] () ParseTree
lemmaParser =
    do  keyword "Lemma:"
        proposition <- many (noneOf "\r\n")
        eol
        manySpacesOrComment
        proof <- inductionProofParser <|> equationProofParser
        manySpacesOrComment
        return (ParseLemma proposition proof)

studentParser ::  Parsec [Char] () [ParseTree]
studentParser =
    do  lemmas <- many1 lemmaParser
        eof
        return lemmas

lineSpaces = skipMany (oneOf " \t") <?> "horizontal white space"

keyword :: String -> Parsec [Char] () ()
keyword kw = try $ do
    string kw
    notFollowedBy alphaNum
    lineSpaces

keywordCase = keyword "Case"
keywordQED = keyword "QED"

caseParser :: Parsec [Char] () (String, ParseEquations)
caseParser = do
        keywordCase
        cons <- many1 (noneOf "\r\n")
        eol
        manySpacesOrComment
        eqns <- manyTill p end
        manySpacesOrComment
        return (cons, eqns)
    where
        p = do
            spaces
            optional (string "= ")
            res <- many1 (noneOf "\r\n")
            eol
            manySpacesOrComment
            return res
        end = lookAhead $ (manySpacesOrComment >> (keywordCase <|> keywordQED))

manySpacesOrComment =
    do
        many space
        optionMaybe (many commentParsers)
        many space
        return ()

