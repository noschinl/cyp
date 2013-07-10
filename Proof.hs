<datatype>
# T b c = H b c | X (T b c) c 
# Tree a = Leaf | Node a (Tree a) (Tree a)
# [a] = [] | a : [a]
# List a = Nil | Cons a (List a)
<datatype>
<Sym>
# (++)
# (+)
# tail
<Sym>
<Anmerkung> 
Aufpassen bei Infix Application! Kein (x) vergessen, mit x = Infix Application! 
<Anmerkung>
<Def>
# length (reverse:reverses) = 1 + length reverses
# length (x:xs) f = 1 `f` length xs
# length [] = 0
# reverse (x:xs) = reverse xs ++ [x]
# reverse [] = []
<Def>
<Lemma>
# length (xs ++ ys) = length xs + length ys
# length (xs ++ ys) = length (ys ++ xs)
# sum (map length ((map reverse xs))) = sum (map length xs)
# sum (map length ((map f xs))) = sum (map length xs)
<Lemma>
<Induction>
length (reverse xs) = length xs
<Induction>
<Over>
xs
<Over>
<BaseCase>
length (reverse []) = length []
<BaseCase>
<Hypothesis>
length (reverse xs) = length xs
<Hypothesis>
<Step>
length (reverse (x:xs)) =
length (reverse xs ++ [x]) = 
length (reverse xs) + length [x] =
length xs + length [x] = 
length (xs ++ [x]) =
length (x:xs)
<Step>
