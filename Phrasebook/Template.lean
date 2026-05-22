/-
Copyright (c) 2026 Your Name Here. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name here
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
-- Write a code block with ```savedLean ... ``` to save it to an external file.
open Verso.Genre.Manual.InlineLean


open Phrasebook

set_option pp.rawOnError true

#doc (Manual) "Tutorial: How to write a polynomial using Mathlib" =>

This page explains how to express a polynomial using the definitions in Mathlib.
We assume basic knowledge of both Lean and polynomials.

First, let's write the type of all univariate polynomials with coefficients in R, with R a semiring.
::: leanSection
```lean
variable {R : Type*} [Semiring R]
```
Now, the type of polynomials over {lean}`R` is {lean}`Polynomial R`.

To say "let f be a polynomial with coefficients in R" you can use
```lean
variable (f : Polynomial R)
```
The notation `R[X]` for the polynomial ring over {lean}`R` is also available,
but is _scoped_ in the {lean}`Polynomial` namespace.
```lean
open scoped Polynomial

variable (f : R[X])
```
The _constant polynomials_ are the image of the coefficient semiring {lean}`R`
in {lean}`R[X]`.
```lean
variable {r : R}
#check (Polynomial.C r : R[X])
```
The variable of the polynomial ring is
```lean
#check (Polynomial.X : R[X])
```
It is common to simply open the {lean}`Polynomial` namespace, not just the _scoped_ notation, to be able to write
```lean
open Polynomial

#check C r + C 2 * X ^ 2 + X ^ 3
```
There is also a specific constructor for monomials, where you specify the
degree and the constant:
```lean
example : monomial 3 r = C r * X ^ 3 := by
  rw [C_mul_X_pow_eq_monomial]
```
There are two notions of _degree_ for polynomials, distinguished by the type in
which they take values:
```lean
#check (natDegree : R[X] → ℕ)
-- and
#check (degree : R[X] → WithBot ℕ)
```
For non-zero polynomials, the `natDegree` and the `degree` agree.
The polynomial `C 0` has `natDegree` equal to `0`, while it has `degree`
equal to `⊥`.
:::
