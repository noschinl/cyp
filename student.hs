Lemma: length (reverse ys) = length ys

Proof by induction on ys

-- Cases

Case Nil
    length (reverse Nil) 
    = length Nil
    
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

Lemma: length (reverse [1,2]) = length [1,2]
Proof
    length (reverse [1,2])
     = length [1,2]
QED
