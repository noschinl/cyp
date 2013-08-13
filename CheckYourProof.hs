module CheckYourProof where
import Data.Char
import Text.Regex
import Data.List
import Language.Haskell.Exts.Parser 
import Language.Haskell.Exts.Syntax(Literal (..), QName(..), SpecialCon (..), Name (..), ModuleName (..), Exp (..), QOp (..))

{-
Copyright by Dominik Durner / Technische Universität München - Institute for Informatics - Chair for Logic and Verification (I21)

Check Your Proof (CYP)
- What is CYP?
		Check your Proof is a functional program for students to check the correctness of their proofs by induction over simple data structures (e.g. List, Trees).

noschinl = Wiweni64
-}

type ConstList = [String]
type VariableList = [String]

proof file =
  do
		content <- readFile file
		(datatype, goals) <- getDataType content "<Datatype>"
		sym <- varToConst $ getSym content "<Sym>"
		(func, globalConstList) <- getFunc content "<Def>" sym
		lemmata <- getCyp content "<Lemma>" globalConstList
		induction <- getCyp content "<Induction>" globalConstList
		hypothesis <- getCyp content "<Hypothesis>" globalConstList
		over <- getOver content "<Over>" globalConstList
		basecase <- getCyp content "<BaseCase>" globalConstList 
		step <- getCyp content "<Step>" globalConstList
		(newlemma, variable, goals, static) <- getFirstStep induction step over datatype
		return ( newlemma, goals, static)

data Cyp = Application Cyp Cyp | Const String | Variable String | Literal Literal | IHConst String
  deriving (Show, Eq)
  
data TCyp = TApplication TCyp TCyp | TConst String | TNRec String | TRec String
	deriving (Show, Eq)

printCypEquoations [] = []
printCypEquoations (x:xs) = [map printInfo x] ++ (printCypEquoations xs)

printRunnable :: Cyp -> String
printRunnable (Application (Variable a) cyp) ="((" ++ a ++ ") " ++ (printRunnable cyp)++ ")"
printRunnable (Application (Const a) cyp) ="((" ++ a ++ ") " ++ (printRunnable cyp)++ ")"
printRunnable (Application cypCurry cyp) = "(" ++ (printRunnable cypCurry) ++ " " ++ (printRunnable cyp) ++ ")"
printRunnable (Literal a) = translateLiteral a
printRunnable (Variable a) = a
printRunnable (Const a) = a
printRunnable (IHConst a) = "'" ++ a

printInfo :: Cyp -> String
printInfo (Application (Variable a) cyp) ="((?" ++ a ++ ") " ++ (printInfo cyp)++ ")"
printInfo (Application (Const a) cyp) ="((" ++   a ++ ") " ++ (printInfo cyp)++ ")"
printInfo (Application cypCurry cyp) = "(" ++ (printInfo cypCurry) ++ " " ++ (printInfo cyp) ++ ")"
printInfo (Literal a) = translateLiteral a
printInfo (Variable a) = "?" ++ a
printInfo (Const a) = a
printInfo (IHConst a) = "'" ++ a

getGoals :: [TCyp] -> TCyp -> Int -> ([TCyp], [String])
getGoals [] _ _ = ([], [])
getGoals (x:xs) goal n = ((fst $ getGoal x goal n): (fst (getGoals xs goal (snd $ getGoal x goal n))), (getConstructorName x): (snd (getGoals xs goal (snd $ getGoal x goal n))))

getGoal :: TCyp -> TCyp -> Int -> (TCyp, Int)
getGoal maybeGoal@(TApplication (TNRec a) cyp) goal n = ((TApplication (TNRec a) (fst $ getGoal cyp goal n)), snd $ getGoal cyp goal n)
getGoal maybeGoal@(TApplication (TConst a) cyp) goal n | maybeGoal == goal = (TRec ((getConstructorName goal) ++ show(n)),  n+1)
																									     | otherwise = ((TApplication (TConst a) (fst $ getGoal cyp goal n)), snd $ getGoal cyp goal n)
getGoal maybeGoal@(TApplication cypCurry cyp) goal n | maybeGoal == goal = (TRec ((getConstructorName goal) ++ show(n)), n+1)
																									   | otherwise = ((TApplication (fst $ getGoal cypCurry goal n) (fst $ getGoal cyp goal (snd $ getGoal cypCurry goal n))), snd $ getGoal cyp goal (snd $ getGoal cypCurry goal n))
getGoal maybeGoal@(TNRec a) goal n = (TNRec a, n)
getGoal maybeGoal@(TConst a) goal n | maybeGoal == goal = (TRec ((getConstructorName goal) ++ show(n)), n+1)
																   	| otherwise = (TConst a, n)
																   	
translateToTyp (Application (Variable a) cyp) = TApplication (TNRec a) (translateToTyp cyp)
translateToTyp (Application (Const a) cyp) = TApplication (TConst a) (translateToTyp cyp)
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
getLists (InfixApp e1 (QConOp i) e2) = ((getConstList $ getLists e1) ++ (getConstList $ getLists e2) ++ [translateQName i], (getVariableList $ getLists e1) ++ (getVariableList $ getLists e2))
getLists (InfixApp e1 (QVarOp i) e2) = ((getConstList $ getLists e1) ++ (getConstList $ getLists e2) ++ [translateQName i], (getVariableList $ getLists e1) ++ (getVariableList $ getLists e2))
getLists (App (Var e1) e2) = ((getConstList $ getLists e2) ++ [translateQName e1], (getVariableList $ getLists e2))
getLists (App e1 e2) = ((getConstList $ getLists e1) ++ (getConstList $ getLists e2), (getVariableList $ getLists e1) ++ (getVariableList $ getLists e2))
getLists (Paren e) = getLists e
getLists (List l) | null(l) = (["[]"], [])
		              | otherwise = ((getConstList $ getLists$ head l) ++ (getConstList $ getLists $ List (tail l)) ++ [":"], (getVariableList $ getLists $ head l) ++ (getVariableList $ getLists $ List (tail l)))
									
getConstList :: (ConstList, VariableList) -> ConstList
getConstList (cons ,_) = cons

getVariableList :: (ConstList, VariableList) -> VariableList
getVariableList (_, var) = var

translate :: Exp -> ConstList -> VariableList -> (String -> [String] -> Bool)-> Cyp
translate (Var v) cl vl f | elem (translateQName v) cl = Const (translateQName v)
													| f (translateQName v) vl = Variable (translateQName v)
translate (Con c) cl vl f = Const (translateQName c)
translate (Lit l) cl vl f = Literal l
translate (InfixApp e1 (QConOp i) e2) cl vl f = Application (Application (Const (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
translate (InfixApp e1 (QVarOp i) e2) cl vl f | elem (translateQName i) cl =  Application (Application (Const (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
					                                    | elem (translateQName i) vl =  Application (Application (Variable (translateQName i)) (translate e1 cl vl f)) (translate e2 cl vl f)
translate (App (Var e1) e2) cl vl f = Application (Const (translateQName e1)) (translate e2 cl vl f)
translate (App e1 e2)  cl vl f = Application (translate e1 cl vl f) (translate e2 cl vl f)
translate (Paren e) cl vl f = translate e cl vl f
translate (List l) cl vl f | null(l) = Const ("[]")
			                     | otherwise = Application (Application (Const (":")) (translate (head l) cl vl f)) (translate (List (tail l)) cl vl f)
								 							 				
translateQName (Qual (ModuleName m) (Ident n)) = m++n
translateQName (Qual (ModuleName m) (Symbol n)) = m ++ n
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

varToConst xs =
  do 
    cyp <- xs
    return (concat $ helper cyp)
      where 
      	helper [] = []
      	helper (x:xs) = helperhelper x : (helper xs)
      	  where 
      	    helperhelper [] = []
      	    helperhelper (x:xs) = transformVartoConst x : (helperhelper xs)
		
transformVartoConst :: Cyp -> Cyp
transformVartoConst (Variable v) = Const v
transformVartoConst (Application (Variable a) cyp) = Application (Const a) (transformVartoConst cyp)
transformVartoConst (Application (Const a) cyp) = Application (Const a) (transformVartoConst cyp)
transformVartoConst (Application cypCurry cyp) = Application (transformVartoConst cypCurry) (transformVartoConst cyp)
transformVartoConst (Literal a) = Literal a


mapGoals :: [[Cyp]] -> [[Cyp]] -> [String] -> [TCyp] -> [([Cyp], [TCyp], [Cyp])]
mapGoals theses firststeps over goals = concatMap (\y -> map (\x -> goalLookup x y (head over) x) goals) (parseFirstStep (head $ head theses) (head $ head firststeps) (head over))

mapFirstStep :: [[Cyp]] -> [[Cyp]] -> [String] -> [TCyp] -> ([[Cyp]], [Cyp], [TCyp], [Cyp])
mapFirstStep theses firststeps over goals = (map (\x -> map (\y -> createNewLemmata y (head over) x) (head theses)) (concatMap fst3 (mapGoals theses firststeps over goals)), concatMap fst3 (mapGoals theses firststeps over goals), concatMap snd3 (mapGoals theses firststeps over goals), concatMap thrd3 (mapGoals theses firststeps over goals))


parseFirstStep :: Cyp -> Cyp -> String -> [Cyp]
parseFirstStep (Variable n) m over | over == n =  [m]
                                   | otherwise = []
parseFirstStep (Literal l) _ _ = []
parseFirstStep (Const c) _ _  = []
parseFirstStep (Application (Variable a) cyp) (Application m thesiscyp) over | over == a = [m]
                                                                             | otherwise = parseFirstStep cyp thesiscyp over
parseFirstStep (Application (Const a) cyp) (Application (Const b) cypthesis) over = parseFirstStep cyp cypthesis over
parseFirstStep (Application cypCurry cyp) (Application cypthesisCurry cypthesis) over = (parseFirstStep cypCurry cypthesisCurry over) ++ (parseFirstStep cyp cypthesis over)
parseFirstStep _ _ _ = []


goalLookup :: TCyp -> Cyp -> String -> TCyp -> ([Cyp], [TCyp], [Cyp])
goalLookup (TApplication (TConst a) tcyp) (Application (Const b) cyp) over x | a == b = goalLookup tcyp cyp over x
																																						 | otherwise = ([], [x], [])
goalLookup (TApplication tcypcurry tcyp) (Application cypcurry cyp)  over x 
	| length (snd3 (goalLookup tcyp cyp over x) ++ snd3 (goalLookup tcypcurry cypcurry over x)) == 0 = (fst3 (goalLookup tcyp cyp over x) ++ fst3 (goalLookup tcypcurry cypcurry over x), snd3 (goalLookup tcyp cyp over x) ++ snd3 (goalLookup tcypcurry cypcurry over x), thrd3 (goalLookup tcyp cyp over x) ++ thrd3 (goalLookup tcypcurry cypcurry over x))
	| otherwise = ([], [], [])

goalLookup (TConst a) (Const b) over x | a == b = ([], [], [])
																		   | otherwise = ([], [x], [])
goalLookup (TNRec a) (Variable b) _ _ = ([], [], [Variable b])
goalLookup (TRec a) (Variable b) over x = ([Variable b], [], [Variable b])
goalLookup (TRec a) (Const b) over x = ([Const b], [], [])
goalLookup _ _ _  x = ([], [x], [])

createNewLemmata :: Cyp -> String -> Cyp -> Cyp
createNewLemmata (Application (Variable a) cyp) over b = Application (Variable a) (createNewLemmata cyp over b)
createNewLemmata (Application (Const a) cyp) over b = Application (Const a) (createNewLemmata cyp over b)
createNewLemmata (Application cypcurry cyp) over b =  Application (createNewLemmata cypcurry over b) (createNewLemmata cyp over b)
createNewLemmata (Variable a) over (Const b) | over == a = Const b
																		 				 | otherwise = Variable a
createNewLemmata (Variable a) over (Variable b) | over == a = Const b
																		 				 		| otherwise = Variable a
createNewLemmata (Const a) over (Const b) | over == a = Const b
																					| otherwise = Const a
createNewLemmata (Const a) over (Variable b) | over == a = Const b
																						 | otherwise = Const a
createNewLemmata (Literal a) _ _ = Literal a

getFirstStep thesis steps over goals =
	do
		return (mapFirstStep thesis steps over goals)

getDataType content expression = 
  do
    foo <- outterParse content expression
    return (getGoals (tail $ head $ (innerParseDataType foo)) (head $ head $ (innerParseDataType foo)) 0)

getCyp content expression global = 
  do
    foo <- outterParse content expression
    return (innerParseCyp foo global)

getSym content expression = 
  do
    foo <- outterParse content expression
    return (innerParseSym foo)

getOver content expression global =
  do
    foo <- outterParse content expression
    return (concat $ map getVariableList (innerParseLists foo))

getFunc content expression sym = 
  do
    foo <- outterParse content expression
    return (parseFunc foo (innerParseLists foo) (nub $ globalConstList (innerParseLists foo) sym), nub $ globalConstList (innerParseLists foo) sym)
		
globalConstList (x:xs) ys = getConstList x ++ (globalConstList xs ys)
globalConstList [] ((Const y):ys) = y : (globalConstList [] ys)
globalConstList [] [] = []

parseFunc r l g = zipWith (\a b -> [a, b]) (innerParseFunc r g l head) (innerParseFunc r g l last)

innerParseFunc [] _ _ _ = []
innerParseFunc (x:xs) g (v:vs) f = (parseDef (f (splitStringAt "=" x [])) g (getVariableList v)):(innerParseFunc xs g vs f)
  where
    parseDef x g v = translate (transform $ parseExp $ x) g v elem

innerParseLists [] = []
innerParseLists (x:xs) = (parseLists $ head (splitStringAt "=" x [])):(innerParseLists xs)
		
parseLists x = getLists $ transform $ parseExp $ x
		
innerParseCyp [] _ = []
innerParseCyp (x:xs) global = parseCyp (splitStringAt "=" x []) global:(innerParseCyp xs global)

parseCyp [] _ = []
parseCyp (x:xs) global = translate (transform $ parseExp x) global [] true : (parseCyp xs global)

innerParseSym [] = []
innerParseSym (x:xs) = parseSym (splitStringAt "=" x []):(innerParseSym xs)

parseSym [] = []
parseSym (x:xs) = (translate (transform $ parseExp x) [] [] true)  : (parseSym xs)

innerParseDataType [] = []
innerParseDataType (x:xs) = parseDataType (splitStringAt "=|" x []):(innerParseDataType xs)

parseDataType [] = []
parseDataType (x:xs) = (translateToTyp (translate (transform $ parseExp x) [] [] true))  : (parseDataType xs)

transform (ParseOk a) = a

outterParse content expression = 
  do
    return $ trim $ deleteAll splitH deleteH
      where
      	deleteH = (\x -> ( x == "") || ( x == expression))
      	splitH = splitStringAt "#" (replace expression "" $ concat matchReg) []
      	  where
      	    matchReg = extract (matchRegex regex (deleteAll content isControl))
      	      where
            		regex = mkRegex (expression ++ "(.*)" ++ expression)
            		extract (Just x) = x
    	
deleteAll :: Eq a => [a] -> (a->Bool) -> [a]
deleteAll [] _ = []
deleteAll (x:xs) a | a x = deleteAll xs a
		               | otherwise = x : (deleteAll xs a)
									 
splitStringAt :: Eq a => [a] -> [a] -> [a] -> [[a]]
splitStringAt a [] h | h == [] = []
		                 | otherwise = h : []
splitStringAt a (x:xs) h | x `elem` a = h : splitStringAt a xs []
			                   | otherwise = splitStringAt a xs (h++[x])
												 
trim (x:xs) = trimh (trimh x):trim xs
  where
    trimh = reverse . dropWhile isSpace
trim [] = []

replace _ _ [] = []
replace old new (x:xs) | isPrefixOf old (x:xs) = new ++ drop (length old) (x:xs)
        							 | otherwise = x : replace old new xs

fst3 (a, _, _) = a
snd3 (_, a, _) = a
thrd3 (_, _, a) = a

