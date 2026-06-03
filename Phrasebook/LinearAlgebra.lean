/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen, Anne Baanen
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


open Phrasebook

set_option pp.rawOnError true



#doc (Manual) "How to write linear algebra using Mathlib" =>

This chapter explains how to express common concepts in linear algebra using the definitions in Mathlib.
We assume basic knowledge of both Lean and linear algebra.

# Modules and vector spaces

Vector spaces and modules are [covered in Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/C10_Linear_Algebra.html#vector-spaces-and-linear-maps);
this section assumes you have read the linked section.
As a complement to MiL, this section of the phrasebook discusses:

* more details on modules and semi-modules
* common examples of modules and vector spaces
* semilinear maps

::: leanSection
```lean -show
variable {x y z : ℤ} {v w : Fin 2 → ℤ}
```

Recall from Mathematics in Lean that
Mathlib has one typeclass called {name}`Module` that can be used in combination with other classes
to express semimodules, modules and vector spaces in a uniform way.
The defining characteristic shared between modules and vector spaces is the properties of their scalar multiplication.
Scalar multiplication is written `(· • ·)` (`\bu`) and called `smul` in declaration names,
so for example distributivity of multiplication is written {lean}`(x * y) • v = x • (y • v)` (see {name}`mul_smul`).

To say `V` is a vector space over the field `K`, write:

```lean
variable {K V : Type*}
  [Field K] [AddCommGroup V] [Module K V]
```
:::

To say `M` is a module over the ring `R`, write:

::: leanSection
```lean
variable {R M : Type*}
  [Ring R] [AddCommGroup M] [Module R M]
```
:::

To say `M` is a semimodule over the semiring `R`, write:

::: leanSection
```lean
variable {R M : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M]
```

The {lean}`Module R M` parameter specifies the behaviour of scalar multiplication, while {lean}`AddCommMonoid M` (and its descendants) and {lean}`Semiring R` (and its descendants) specify behaviour of operations that stay within {lean}`M` and {lean}`R` respectively, such as `(· + ·)` and `(· * ·)` respectively.

In this document, we'll use "module" to mean "semimodule, module, or vector space" and "ring" to mean "semiring, ring, or field" if the distinction between those does not matter.
:::

::: leanSection
```lean -show
variable {R M : Type*}
```

Lean *cannot* automatically infer that {lean}`M` has negation if {lean}`R` has,
because a priori it cannot guess the correct {lean}`R` given an arbitrary {lean}`M`.
So if we declare variables like:
```lean
variable [Ring R] [AddCommMonoid M] [Module R M]
```
then trying to negate elements of {lean}`M` will fail.

```lean +error (name := negError)
#check fun x : M => -x
```
```leanOutput negError
failed to synthesize instance of type class
  Neg M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
The solution is to either declare \[{lean}`AddCommGroup M`\] in your variables,
or to add the instance inline using {lean}`Module.addCommMonoidToAddCommGroup`.

:::

## Examples of modules

```lean -show
variable {i j : Type} {n : ℕ} {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {x : M}
```

The {lean}`n`-dimensional free module over the ring {lean}`R` is written {lean}`Fin n → R`.
Mathlib provides a module structure on the function type {lean}`i → R` for any type `i`.
It is generally a good idea to use {lean}`i → R` instead of {lean}`Fin n → R`,
unless the order of the indexing elements matters.

The _direct sum_ of copies of `R` is written {lean}`i →₀ R`,
and the linear equivalence with {lean}`i → R` in the finite case is called {name}`Finsupp.linearEquivFunOnFinite`.

A ring is a module over itself, with scalar multiplication equal to multiplication.
This module structure is found by typeclass inference. Use {name}`smul_eq_mul` to state this equality.

Finally, an additive monoid {lean}`M` is a module over the natural numbers,
with the scalar multiplication {lean}`n • x` defined as `x + x + ... + x`, {lean}`n` times.
Analogously, additive groups are modules over the integers.
These module structures are found by typeclass inference.

## Linear maps and semilinear maps

```lean -show
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
```

Recall from [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/C10_Linear_Algebra.html#linear-maps) the definition of a linear map in Mathlib:
For two {lean}`R`-modules {lean}`M₁`, {lean}`M₂`,
the type {lean}`M₁ →ₗ[R] M₂` (called {name}`LinearMap` in declaration names)
contains the bundled {lean}`R`-linear maps from {lean}`M₁` to {lean}`M₂`.
These are maps that preserve zero (see {name}`map_zero`), addition (see {name}`map_add`) and scalar multiplication (see {name}`map_smul`).
The type {lean}`M₁ ≃ₗ[R] M₂` (called {name}`LinearEquiv`) contains the bundled {lean}`R`-linear equivalences
between {lean}`M₁` and {lean}`M₂`: these are the invertible linear maps.

```lean -show
variable {S N : Type*} [Ring S] [AddCommGroup N] [Module S N] (σ : R →+* S) (σ' : S →+* R) (f : M →ₛₗ[σ] N)
```
In Mathlib, the types {name}`LinearMap` and {name}`LinearEquiv` actually denote _semi_linear maps and equivalences.
If {lean}`N` is an {lean}`S`-module and {lean}`(σ : R →+* S)` is a ring homomorphism, then
a semilinear map `(f : M →ₛₗ[σ] N)` preserves scalar multiplication only up to {lean}`σ`:

```lean (name := map_smulSL)
#check map_smulₛₗ f
```
```leanOutput map_smulSL
map_smulₛₗ f : ∀ (c : R) (x : M), f (c • x) = σ c • f x
```
The notation {lean}`M₁ →ₗ[R] M₂` stands for {lean}`M₁ →ₛₗ[RingHom.id R] M₂`.
Since {name}`LinearMap` can denote both linear and semilinear map,
it is clearer to always use the `→ₗ` and `→ₛₗ` notation.

```lean -show
variable {T : Type*} [Ring T] (τ : S →+* T)

open ComplexConjugate
```
Composing a {lean}`σ`-semilinear and a {lean}`τ`-semilinear map requires Lean to
figure out the composition of {lean}`σ` with {lean}`τ`.
In order to do so, you need to have declared an instance of {lean}`RingHomCompTriple σ τ _`.
For example, that two conjugate-linear maps compose to form a linear map would be expressed
by an instance of type {lean}`RingHomCompTriple conj conj (RingHom.id ℂ)`.

Semilinear equivalences are the analogous generalization of linear equivalences,
also requiring that the ring homomorphism {lean}`σ` be invertible.
The {name}`RingHomInvPair` class expresses this condition.
If you use a ring homomorphism without further assumptions, you will see an error like:
```lean (name := semiLinearEquiv_error) +error
example (σ : R →+* S)
    (e : M ≃ₛₗ[σ] N) : N ≃ₛₗ[σ] M := e.symm
```
```leanOutput semiLinearEquiv_error
failed to synthesize instance of type class
  RingHomInvPair σ ?m.25

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

The fix is to add the inverse map {lean}`(σ' : S →+* R)` and two {name}`RingHomInvPair` instances to the context.
The inverse map will be automatically picked up by {name}`LinearEquiv.symm`.
```lean
example (σ : R →+* S) (σ' : S →+* R)
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] N) : N ≃ₛₗ[σ'] M := e.symm
```

Note that there is no automatic {name}`RingHomInvPair` instance for ring isomorphisms:
```lean +error
example (σ : R ≃+* S) (e : M ≃ₛₗ[σ.toRingHom] N) :
    N ≃ₛₗ[σ.symm.toRingHom] M := e.symm
```
```lean -show
variable (σ : R ≃+* S)
```
Instead, define instances for specific values of {lean}`σ`.
Beware that an instance of the form {lean}`RingHomInvPair σ.toRingHom σ.symm.toRingHom` where `σ` is a variable
will result in `e.symm.symm` getting the type `M ≃ₛₗ[σ.symm.symm] N` instead of the expected `M ≃ₛₗ[σ] N`.

Background reading on semilinear maps in Mathlib is available in the article [Frédéric Dupuis, Robert Y. Lewis, and Heather Macbeth. Formalized functional analysis with semilinear maps. In ITP 2022](https://doi.org/10.4230/LIPIcs.ITP.2022.10).
