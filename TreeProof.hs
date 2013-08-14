<Datatype>
# Tree a = Leaf | SingleNode (Tree a) | Node a (Tree a) (Tree a)
<Datatype>
<Sym>
# (++)
# (+)
# tail
# length
# reverse
<Sym>
<Def>
head (a:(head (x:xs))) 
<Def>
<Lemma>

<Lemma>
<Induction>
length (reverse t) = length t
<Induction>
<Over>
t
<Over>
<BaseCase>
length (reverse Leaf) = length Leaf
<BaseCase>
<Step>
length (reverse (Node 0 a b)) = length (Node 0 a b)
<Step>
