goal length (reverse zs) .=. length zs
goal length (reverse (1 : ys)) .=. 1 + length ys

data List a = [] | a : (List a)
data Tree a = Leaf | Tree a (Tree a) (Tree a)

declare_sym (+)
declare_sym (++)
declare_sym tail
declare_sym map
--Aufpassen bei Infix Application! Kein (x) vergessen, mit x = Infix Application! 


axiom ys ++ [y] .=. (y:ys)
axiom length (xs ++ ys) .=. length xs + length ys
axiom length (xs ++ ys) .=. length (ys ++ xs)

axiom sum (map length ((map reverse xs))) .=. sum (map length xs)
axiom sum (map length ((map f xs))) .=. sum (map length xs)


length (reverse:reverses) = 1 + length reverses
length (x:xs) f = 1 `f` length xs

length [] = 0

reverse (x:xs) = (reverse xs) ++ [x]
reverse [] = []
