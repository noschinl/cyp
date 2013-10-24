Lemma: length (reverse ys) = length ys

Proof by induction on List ys

-- Cases

Case []
    length (reverse []) 
    = length []
    
{-Between Case-}

Case :
    length (reverse (x:xs))
    = length (reverse xs ++ [x])
    = length (reverse xs) + length [x] --Sepp
    = length xs + length [x]

    length (x:xs)
    = length (xs ++ [x])
    = length xs + length [x]
{-After Hier darf kein C sein _ase-}
QED
{-Between Lemma 
Lemma: length (reverse ys) = length ys

Proof by equotions
Proof by biatch-
q.e.d.-}

Lemma: length (reverse (1 : ys)) = 1 + length ys
Proof
    length (reverse (1 : ys))
    = length (1 : ys)
    = 1 + length ys
QED
