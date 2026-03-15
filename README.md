[![Lean 4 Build](https://github.com/adityabagchi2002-boop/Non-Trivial-Cycle-Refutation-in-Collatz-Dynamics-/actions/workflows/build.yml/badge.svg)](https://github.com/adityabagchi2002-boop/Non-Trivial-Cycle-Refutation-in-Collatz-Dynamics-/actions/workflows/build.yml)
https://doi.org/10.5281/zenodo.19034964
# Non-Trivial-Cycle-Refutation-in-Collatz-Dynamics-
This is a Lean 4 formalization of the manuscript that refutes non-trivial integer cycle in Collatz conjecture with no axiom beyond Mathlib. 
# Formal Refutation of Non-Trivial Cycles for the Accelerated Collatz Operator

**Author:** Aditya Bagchi  
**Associated Manuscript:** *A Deterministic Analysis of Integer Cycles in Collatz Dynamics*

## Overview
This repository contains the complete, axiom-free Lean 4 formalization refuting the existence of non-trivial cycles for the accelerated Collatz (Syracuse) operator. 

While historical approaches to the Collatz conjecture rely on probabilistic heuristics, transcendence theory, or massive computational brute force, this project introduces a deterministic topological approach. The codebase formally verifies that the `1 -> 4 -> 2 -> 1` loop is the strict mathematical equilibrium state, and proves that any deviation from this state results in a terminal Diophantine or 3-adic contradiction.

## Verification Guarantee
This proof is certified by the Lean 4 kernel. It relies **only** on foundational Lean 4 Mathlib axioms. It contains absolutely zero `sorry` tags or unverified heuristic assumptions. 

Executing the terminal command `#print axioms Theorem1_Cycle_Topologies_Refuted` yields only the foundational rules of classical logic (`propext`, `Classical.choice`, `Quot.sound`).

## Mapping the Code to the Manuscript
The Lean 4 codebase strictly mirrors the logical progression of Theorem 1 in the associated manuscript:

* **The Equilibrium State (Lemma 1A):** Verifies that a trajectory with uniform division exponents ($a_i = 2$) strictly forces the core integer solution $x = 1$.
* **Pure Positive Topology (Lemma 1D):** Verifies that exclusively positive perturbations force the algebraic denominator to outgrow the numerator ($D_{new} > N_{new}$), violating the cycle condition.
* **Pure Negative Topology (Lemmas 1C & 1E):** Verifies that negative perturbations introduce an irrecoverable 3-adic valuation deficit ($v_3 < n$) that mathematically annihilates the divisibility requirement.
* **Mixed Topology (Lemmas 1F, 1G, & 1H):** Verifies the Principle of Net Algebraic Cost. Any positive perturbation required to repair a 3-adic valuation drop incurs an exponential magnitude cost, triggering a structural algebraic collapse.
* **Master Signature (Theorem 1):** The final aggregate theorem (`Theorem1_Cycle_Topologies_Refuted`) exhaustively routes every possible trajectory state to `False`.

## How to Compile and Verify
To audit this proof on your local machine:

1. Ensure you have [Lean 4 and Lake](https://leanprover.github.io/lean4/doc/setup.html) installed.
2. Clone this repository:
   ```bash
   git clone [https://github.com/adityabagchi2002-boop/collatz-cycle-refutation.git](https://github.com/adityabagchi2002-boop/collatz-cycle-refutation.git)
N.B: The code compiles in live lean-lang.org. 
