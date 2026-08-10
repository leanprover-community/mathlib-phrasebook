/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
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

#doc (Manual) "Clifford, exterior algebras" =>

We describe Mathlib's theory of Clifford algebras. We also describe the
exterior algebra, which is implemented as the Clifford algebra of the trivial
quadratic form.

# Clifford algebras

To construct a Clifford algebra we must first give ourselves a quadratic form:
```lean
variable (R M : Type*)
  [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)
```
Given this data we may construct the associated Clifford algebra $`Cl(Q)` as follows:
```lean
#check CliffordAlgebra Q
```
We can witness that this has the structure of an $`R`-algebra as follows:
```lean
#synth Algebra R (CliffordAlgebra Q)
```
The natural map from the module $`M` into the Clifford algebra $`ι : M → Cl(Q)` is
written in Mathlib as {lean}`CliffordAlgebra.ι Q`. We may witness that this obeys
the defining equation as follows:
```lean
open CliffordAlgebra in
example (m : M) :
    (ι Q m) ^ 2 = Q m • 1 := by
  rw [sq, ι_sq_scalar, Algebra.smul_def, mul_one]
```
This also shows that Mathlib's Clifford algebras adopt the positive sign convention.

# The universal property

The universal property of the Clifford algebra $`Cl(Q)` states that if $`A` is a
unital, associative $`R`-algebra, then any linear map $`f : M → A` such that
$`f(m) ^ 2 = Q(m)1` factors as a composition of the Clifford map $`ι : M → Cl(Q)`
and a morphism of algebras $`Cl(Q) → A`.

This universal property is expressed in Mathlib as {name}`CliffordAlgebra.lift`.
We can witness some of its properties as follows:
```lean
open CliffordAlgebra

variable (A : Type*) [Ring A] [Algebra R A]
  (f : M →ₗ[R] A)
  (hf : ∀ m, f m * f m = algebraMap _ _ (Q m))

-- The spelling `hf` above is convenient below and is
-- trivially equivalent to the more familiar spelling.
example (m : M) :
    f m * f m = algebraMap _ _ (Q m) ↔
    (f m) ^ 2 = Q m • 1 := by
  simp [sq, Algebra.smul_def, mul_one]

-- The induced map, as a morphism of algebras:
#check lift Q ⟨f, hf⟩

-- This is a factorisation of our original map:
example : lift Q ⟨f, hf⟩ ∘ ι Q = f := by
  ext; simp
```

# Exterior algebras and powers

The exterior algebra is:
```lean
#check ExteriorAlgebra R M
```
Given a natural number $`n` the exterior power $`∧^n M` is called
{name}`ExteriorAlgebra.exteriorPower` and it has a special notation as follows:
```lean
variable (n : ℕ)
#check ⋀[R]^n M
```
Mathlib knows that these submodules constitute a grading of the exterior algebra:
```lean
#synth GradedAlgebra (fun i ↦ ⋀[R]^i M)
```
