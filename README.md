# cyp

![Build status](https://github.com/lukasstevens/cyp/workflows/test/badge.svg)

cyp (short for "Check Your Proof") verifies proofs about Haskell-like programs. It is designed as an teaching aid for undergraduate courses in functional programming. 

The implemented logic is untyped higher-order equational logic, but without lambda expressions. In addition, structural induction over datatypes is supported.

The terms follow standard Haskell-syntax and the background theory can be constructed from datatype declarations, function definitions and arbitrary equations.

The use of this tool to verify Haskell functions is justified by the following considerations:

  * [Fast and Loose Reasoning is Morally Correct](http://www.cse.chalmers.se/~nad/publications/danielsson-et-al-popl2006.html).
  * We convinced ourselves that for a type-correct background-theory and a type-correct proposition a proof exists if and only if a type-correct proof exists. A formal proof is still missing. Here, type-correct is meant in the sense of Haskell's type system, but without type-classes.


## Getting started

Clone the repository to some directory and run
```
stack build
stack test # optional: run the tests
```
To run the binary execute
```
stack run cyp
```
You may also install the binary with
```
stack install
```
This places a binary `cyp` in the `~/.local/bin` folder.
Provided that `~/.local/bin` is in your `PATH`, you can then check a proof by running
```
cyp <background.cthy> <proof.cprf>
```

where `<background.cthy>` defines the program and available lemmas and `<proof.cprf>` contains the proof to be checked.

The source code for cyp also contains some example theories and proofs (look for the files in `test-data/pos`).


## Syntax of Proofs

A proof file can contain an arbitrary number of lemmas. Proofs of later lemmas can use the the previously proven lemmas. Each lemma starts with stating the equation to be proved:
```
Lemma: <lhs> .=. <rhs>
```

where `<lhs>` and `<rhs>` are arbitrary Haskell expressions. cyp supports plain equational proofs as well as proofs by structural or computation induction. An equational proof is introduced by the
```
Proof
```

keyword and followed by one or two lists of equations:
```
                   <term a1>
(by <reason>)  .=. <term a2>
                .
                .
                .
(by <reason>)  .=. <term an>

                   <term b1>
(by <reason>)  .=. <term b2>
                .
                .
                .
(by <reason>)  .=. <term bn>
```
Each term must be given on a separate line and be indented by at least one space. If two lists are given, they are handled as if the second list was reversed and appended to the first. An equational proof is accepted if

  * The first term is equal to `<lhs>` and the last term is equal to `<rhs>`
  * All steps in the equation list are valid. A step `<term a> .=. <term b>` is valid if `<term a>` can be rewritten to `<term b>` (or vice versa) by applying a single equation (either from the background-theory or from one of the previously proven lemmas).

The proof is then concluded by
``` 
QED
```
A proof by structural induction is introduced by the line
```
Proof by induction on <type> <var>
```
where `<var>` is the Variable on which we want to perform induction on `<type>` is the name of the datatype this variable has. Then, for each constructor `<con>` of `<type>`, there must be a line
```
Case <con>
```
After that, the corresponding subgoal and if needed, an induction hypothesis have to be stated:
```
To show: <subgoal>
IH: <induction hypothesis>
```
followed by the keyword 
```
Proof
```
and a list of equations, like for an equational proof. Again, the proof is concluded by:
```
QED
```

Proofs by computation inductions are introduced by the line
```
Proof by computation induction on <args> with <func>
```
where `<func>` is the name of the function we want to perform induction on and `<args>` its formal parameters. For each defining equation of `<func>`, there has to be a line
```
Case <number>
```
where `<number>` indicates the number of the respective equation. Once again, the matching subgoal, the induction hypothesis' if required and the `Proof` keyword are needed. Then, a list of equations follows and the proof is concluded by
```
QED
```
For another overview on cyp syntax and some intuition behind proofs, refer to the [cheatsheet](cheatsheet.md).

## Known limitations

  * There is no check that the functions defined in the background theory terminate (on finite inputs). The focus of this tool is checking the proofs of students against some known-to-be-good background theory.
