
# STAT 4052 - Bayes' Theorem

## Project Description
This project uses Lean 4 and Mathlib to formally verify
Bayes' Theorem using probability measures and
conditional probabilities.

## Main Theorem
Bayes' Theorem relates conditional probabilities:

P(A|B) = P(B|A) * P(A) / P(B)

## Assumptions
The main theorem assumes a probability measure
and nonzero probabilities for events A and B.

No additional external axioms are introduced beyond
the theorem hypotheses and standard Lean/Mathlib
foundations.

## Main Files
- STAT4052BayesTheorem/Basic.lean:
  Contains the definitions and proofs.

## Build Instructions
1. Install Lean 4 using elan.
2. Clone this repository.
3. Open a terminal in the project folder.
4. Run `lake exe cache get`.
5. Run `lake build`.

## Authors
Olawutoni Faseemo, Jingshi Xu, Wentao Ding, Justin Wussler
