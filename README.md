cyp
===

cyp (short for "Check Your Proof") verifies proofs about Haskell-like programs. It is designed as an teaching aid for undergraduate courses in functional programming. 

The implemented logic is untyped higher-order equational logic, but without lambda expressions. In addition, structural induction over datatypes is supported.

The terms follow standard Haskell-syntax and the background theory can be constructed from datatype declarations, function definitions and arbitrary equations.

The use of this tool to verify Haskell functions is justified by the following considerations:

  * [Fast and Loose Reasoning is Morally Correct](http://www.cse.chalmers.se/~nad/publications/danielsson-et-al-popl2006.html).
  * We convinced ourselves that for a type-correct background-theory and a type-correct proposition a proof exists if and only if a type-correct proof exists. A formal proof is still missing. Here, type-correct is meant in the sense of Haskell's type system, but without type-classes.

Getting started
--------------------

Extract the program to some directory and run

    cabal configure
    cabal build

This produces a binary `cyp` in the `dist/build/cyp` folder. You can then check a proof by running

    cyp <background.cthy> <proof.cprf>

where `<background.cthy>` defines the program and available lemmas and `<proof.cprf>` contains the proof to be checked.


Known limitations
-----------------------

  * There is no check that the functions defined in the background-theory terminate (on finite inputs). The focus of this tool is checking the proofs of students against some known-to-be-good background theory.
