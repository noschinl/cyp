-- MUST FAIL, as x:x is not a valid instantiation for case ":"
Lemma: length (reverse ys) .=. length ys

Proof by induction on List ys

-- Cases

Case []
    length (reverse []) 
    .=. length []
    
{-Between Case-}

Case :
    length (reverse (x:x))
    .=. length (reverse x ++ [x])
    .=. length (reverse x) + length [x] --Sepp
    .=. length x + length [x]

    length (x:x)
    .=. length (x ++ [x])
    .=. length x + length (x : [])
{-After Hier darf kein C sein _ase-}
QED
{-Between Lemma 
Lemma: length (reverse ys) .=. length ys

Proof by equotions
Proof by biatch-
q.e.d.-}

Lemma: length (reverse (1 : ys)) .=. 1 + length ys
Proof
    length (reverse (1 : ys))
    .=. length (1 : ys)
    .=. 1 + length ys
QED
