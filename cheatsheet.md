# Proving fun stuff with **CYP**! 

Basic proof structure in .cprf:
* state your lemma/goal
* apply **equivalences from .cthy file** or **earlier lemmas** to prove it!
* use `.=.` for equivalence
* provide applied **rule** for each step!

Rules may be:
* function/data type definitions: `(by def something)`
* lemmas we have already proven `(by lemma_name)`
* an induction hypothesis: `(by IH)`

---

## Equality Proof
Either directly transform the left side into the right...

    Lemma <optional name>: <left_side> .=. <right_side>
    Proof
                        <left_side> 
        (by <rule>) .=. ...
        (by <rule>) .=. <right_side>
    QED

...or transform both into another expression!

    Lemma <optional name>: <left_side> .=. <right_side>
    Proof
                        <left_side> 
        (by <rule>) .=. ...
        (by <rule>) .=. <subgoal>

                        <right_side> 
        (by <rule>) .=. <...>
        (by <rule>) .=. <subgoal>
    QED

---

## Structural Induction

Note that...
* we typically have one case per constructor
* we may need more than one induction hypothesis!

General proof structure:

    Lemma <optional_name>: <left_side> .=. <right_side>

    Proof by induction on <data_type> <variable_name>

    Case <base_case>
        To show: <lemma_for_base_case>
        
        Proof
            ...
        QED

    Case <other_case>
        To show: <lemma_for_other_case>
            IH: <induction_hypothesis>

            Proof
                ...
            QED
    QED


---

## Computation Induction

Think: induction over recursion depth!
Note that...
* we typically have one case per function equation
* cases are **numbered** this time
* if there is no recursive call in an equation, the corresponding case is a **base case**
* for **recursion step** cases: we need one induction hypothesis for each recursive call in an equation - so if one equation has `i` recursive calls, the corresponding case has `i` induction hypothesis'
* the induction variables correspond to the function parameters

General proof structure:

    Lemma <optional_name>: <left_side> .=. <right_side>

    Proof by computation induction on <variables> with <function_name>

    Case 1
        To show: <lemma_for_recursion_base>
        
        Proof
            ...
        QED

    Case 2
        To show: <lemma_for_next_equation>
            IH: <induction_hypothesis>

            Proof
                ...
            QED
    QED

If more than one induction hypothesis is needed, we conventionally number them:

    IH1: ...
    IH2: ...

Disclaimer: cyp currently does not support computational inductions with functions where a recursive call occurs in an `if`-statement. Keep that in mind in case you want to come up with your own proofs for practice!