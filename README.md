simply-typed-proofs
====

I started this project to implement a toy proof system for SAT/UNSAT
using the lambda calculus. Those are modeled using Redex in `base.rkt`,
`sat.rkt`, and `unsat.rkt`

Then I had a thought that LTAC for Coq is just a terrible
meta-programming language. The term language is also kind of terrible to
write. So really what I'd like in a theorem prover is a good term
language, and really meta-programming. So I implemented a theorem prover
for the SAT system to see if this thought had merit. Those are in
`proofs.rkt`, `tactics.rkt`, and `theorems.rkt`

`examples.rkt` contains examples of how to use.
