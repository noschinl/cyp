data List a = [] | a : (List a)
data Tree a = Leaf | Tree a (Tree a) (Tree a)

declare_sym (+)
declare_sym (++)
declare_sym tail
--Aufpassen bei Infix Application! Kein (x) vergessen, mit x = Infix Application! 


lemma ys ++ [y] = (y:ys)
lemma length (xs ++ ys) = length xs + length ys
lemma length (xs ++ ys) = length (ys ++ xs)

lemma sum (map length ((map reverse xs))) = sum (map length xs)
lemma sum (map length ((map f xs))) = sum (map length xs)


length (reverse:reverses) = 1 + length reverses
length (x:xs) f = 1 `f` length xs

length [] = 0

reverse (x:xs) = (reverse xs) ++ [x]
reverse [] = []
