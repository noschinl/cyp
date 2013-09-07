<Annotation>
{-
Lemma mirror (mirror t) = t
Proof by structural induction on t

Base case:
To show: mirror (mirror Empty) = Empty
mirror (mirror Empty)
== mirror Empty             (by mirror_Empty)
== Empty                    (by mirror_Empty)

Induction step:
IH1: mirror (mirror l) = l
IH2: mirror (mirror r) = r
To show: mirror (mirror (Node x l r)) = Node x l r
mirror (mirror (Node x l r))
== mirror (Node x (mirror r) (mirror l))              (by mirror_Node)
== Node x (mirror (mirror l)) (mirror (mirror r))     (by mirror_Node)
== Node x l (mirror (mirror r))                       (by IH1)
== Node x l r                                         (by IH2)

QED
-}
<Annotation>
<Datatype>
# Tree a = Empty | Node a (Tree a) (Tree a)
<Datatype>
<Sym>
# (++)
# (+)
<Sym>
<Def>
# mirror Empty = Empty
# mirror (Node x l r) = Node x ( mirror r ) ( mirror l )
<Def>
<Lemma>
mirror (mirror t) = t
<Lemma>
<Induction>
mirror (mirror t) = t
<Induction>
<Over>
t
<Over>
<Empty>
mirror (mirror Empty)
= mirror Empty
= Empty 
<Empty>
<Node>
mirror (mirror (Node x l r))
= mirror (Node x (mirror r) (mirror l))              
= Node x (mirror (mirror l)) (mirror (mirror r))    
= Node x l (mirror (mirror r))                      
= Node x l r      
<Node>
