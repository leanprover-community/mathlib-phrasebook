/-
Copyright (c) 2026 The Mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mathlib Community
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Phrasebook

set_option pp.rawOnError true

#doc (Manual) "How to work with number fields using Mathlib" =>

This page explains how to express the basic objects of algebraic number theory using
the definitions in Mathlib: number fields, their rings of integers, ideals, units, the
class group and the discriminant.
We assume familiarity with both Lean and a first course in algebraic number theory,
at the level of Marcus' *Number Fields*.

# Number fields

::: leanSection
```lean -show
open NumberField Module
variable {K : Type*} [Field K] [NumberField K]
```
A *number field* is a finite extension of {lean}`ℚ`.
In Mathlib this is the {name}`NumberField` class, a `Prop`-valued predicate on a field.
To say "let `K` be a number field", supply *both* a {name}`Field` instance and a
{name}`NumberField` instance:
```lean
variable (K : Type*) [Field K] [NumberField K]
```
The {lean}`Field K` instance cannot be omitted: {name}`NumberField` takes it as a
parameter rather than extending it, so writing only `[NumberField K]` gives an error.
The class itself bundles {name}`CharZero` and {lean}`FiniteDimensional ℚ K`,
which Lean recovers automatically once the two instances above are in scope:
```lean
example : CharZero K := inferInstance
example : FiniteDimensional ℚ K := inferInstance
```

The *degree* `[K : ℚ]` of the number field is its dimension as a {lean}`ℚ`-vector space,
{lean}`Module.finrank ℚ K`:
```lean
#check (Module.finrank ℚ K : ℕ)
```
Avoid using {lean}`Module.rank` for the degree: it is cardinal-valued, whereas a number
field's degree is a natural number.
:::

# The ring of integers

::: leanSection
```lean -show
open NumberField Module
variable {K : Type*} [Field K] [NumberField K]
```
The ring of integers of {lean}`K` is {name}`NumberField.RingOfIntegers`, defined as the
integral closure of {lean}`ℤ` in {lean}`K`.
The scoped notation {lean}`𝓞 K` (type `\McO`) becomes available after `open NumberField`:
```lean
open NumberField

#check (𝓞 K : Type _)
```
An element of {lean}`𝓞 K` is a bundled pair of an element of {lean}`K` together with a
proof that it is integral over {lean}`ℤ`; the coercion {lean}`((↑·) : 𝓞 K → K)` recovers
the underlying element of {lean}`K`.

As an abstract structure, {lean}`𝓞 K` is everything you expect.
It is a commutative ring, and also a *Dedekind domain*: in particular all the various properties
of ideals, like unique factorization, are known.
```lean
example : IsDedekindDomain (𝓞 K) := inferInstance
```
As a {lean}`ℤ`-module it is free of finite rank, and that rank equals the degree of the
field. The freeness and finiteness are found by instance search,
```lean
example : Module.Free ℤ (𝓞 K) := inferInstance
example : Module.Finite ℤ (𝓞 K) := inferInstance
```
and the equality of ranks is {name}`NumberField.RingOfIntegers.rank`:
```lean
example : Module.finrank ℤ (𝓞 K) = Module.finrank ℚ K :=
  RingOfIntegers.rank K
```
:::

::: leanSection
```lean -show
open NumberField
variable {K : Type*} [Field K] [NumberField K]
```
The fact that {lean}`𝓞 K` *is* the integers of {lean}`K` (that an algebraic integer's
minimal polynomial over {lean}`ℚ` already has coefficients in {lean}`ℤ`) is the statement
that {lean}`ℤ` is integrally closed, recorded as an instance:
```lean
example : IsIntegrallyClosed ℤ := inferInstance
```
The general lemma turning this into a statement about minimal polynomials is
{name}`minpoly.isIntegrallyClosed_eq_field_fractions`: over an integrally closed domain,
the minimal polynomial computed over the ring agrees with the one computed over its
field of fractions.
:::

# Ideals

::: leanSection
```lean -show
open NumberField Ideal
variable {K : Type*} [Field K] [NumberField K]
```
Ideals of the ring of integers are values of {name}`Ideal`:
```lean
variable (I : Ideal (𝓞 K))
```
The ideals form a commutative semiring, like the semiring of natural numbers, a ring without subtraction, under addition and multiplication. Because {lean}`𝓞 K` is a Dedekind domain, this semiring is a unique factorization monoid: every nonzero ideal factors uniquely as a product of prime ideals. Both facts are available by instance search. In Lean, a UFD is called {name}`UniqueFactorizationMonoid`, since its definition does not use addition:
```lean
example : CommSemiring (Ideal (𝓞 K)) := inferInstance
example : UniqueFactorizationMonoid (Ideal (𝓞 K)) :=
  inferInstance
```
Concretely, the prime/maximal coincidence and unique factorization let you reason about
ideals through {name}`UniqueFactorizationMonoid` and the prime-ideal API, rather than by
choosing generators.
:::

## The ideal norm

::: leanSection
```lean -show
open NumberField Ideal
variable {K : Type*} [Field K] [NumberField K] (I : Ideal (𝓞 K))
```
The *absolute norm* of an ideal is its index, {name}`Ideal.absNorm`, the cardinality of the
finite quotient {lean}`𝓞 K ⧸ I`.
It is bundled as a monoid-with-zero homomorphism, so multiplicativity is part of the
definition:
```lean
#check (Ideal.absNorm : Ideal (𝓞 K) →*₀ ℕ)

example (I J : Ideal (𝓞 K)) :
    absNorm (I * J) = absNorm I * absNorm J :=
  map_mul absNorm I J
```
Because it is a bundled hom, apply general lemmas like {name}`map_mul` and {name}`map_one`
to it rather than looking for `absNorm`-specific versions.
The norm of a principal ideal is the absolute value of the element norm,
{name}`Ideal.absNorm_span_singleton`.
:::

## Splitting of primes in an extension

An extension `L`/`K` of number fields is set up as:
::: leanSection
```lean
variable {K L : Type*} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
```

```lean -show
open NumberField Ideal
variable (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L))
```

A prime {lean}`p` of {lean}`𝓞 K` decomposes into primes
{lean}`P` of {lean}`𝓞 L` lying over it.
Each such {lean}`P` carries two invariants:

* the *ramification index* {name}`Ideal.ramificationIdx`, the exponent of {lean}`P` in the
  factorization of the extended ideal;
* the *inertia degree* {name}`Ideal.inertiaDeg`, the degree of the residue field extension.

The finite set of primes lying over {lean}`p` is
{name}`IsDedekindDomain.primesOverFinset`, and the fundamental identity
`∑ over P of (e P * f P) = [L : K]` is {name}`sum_ramification_inertia_eq_finrank`.
:::

# The discriminant

::: leanSection
```lean -show
open NumberField Module
variable {K : Type*} [Field K] [NumberField K]
```
The *(absolute) discriminant* of a number field is {name}`NumberField.discr`, an integer computed from
an integral basis of {lean}`𝓞 K`:
```lean
#check (NumberField.discr K : ℤ)
```
It is never zero, {name}`NumberField.discr_ne_zero`:
```lean
example : discr K ≠ 0 := discr_ne_zero K
```
Two theorems connect the discriminant to the other invariants on this page.
The Hermite–Minkowski bound {name}`NumberField.abs_discr_gt_two` states that any number
field other than {lean}`ℚ` has `|discr K| > 2`.
The Minkowski bound
{name}`NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr` produces, in every
ideal class, an ideal whose norm is bounded in terms of `√|discr K|`; this is exactly the
input that makes the class group finite.
:::

# Units

::: leanSection
```lean -show
open NumberField Module
variable {K : Type*} [Field K] [NumberField K]
```
The unit group of the ring of integers is the group of units {lean}`(𝓞 K)ˣ`:
```lean
open NumberField

#check ((𝓞 K)ˣ : Type _)
```
Dirichlet's unit theorem describes its structure: {lean}`(𝓞 K)ˣ` is a finitely generated
abelian group, the product of a finite torsion subgroup and a free part of rank
`r₁ + r₂ - 1`, where `r₁` and `r₂` count the real and complex places.

The unit group is written *multiplicatively*, but Dirichlet's theorem is a statement about
it as a {lean}`ℤ`-module, so Mathlib phrases the rank through {name}`Additive`, which
reinterprets a multiplicative group additively.
Finiteness as a module is an instance,
```lean
example : Module.Finite ℤ (Additive (𝓞 K)ˣ) :=
  inferInstance
```
and its rank is {name}`NumberField.Units.finrank_eq`, where the right-hand side
{name}`NumberField.Units.rank` is defined as `card (InfinitePlace K) - 1 = r₁ + r₂ - 1`:
```lean
#check (NumberField.Units.finrank_eq K)
```
:::

::: leanSection
```lean -show
open NumberField
variable {K : Type*} [Field K] [NumberField K]
```
Two further invariants attached to the units are the *regulator*
{name}`NumberField.Units.regulator`, the covolume of the unit lattice,
```lean
#check (NumberField.Units.regulator K : ℝ)
```
and the order of the torsion subgroup (the roots of unity in {lean}`K`),
{name}`NumberField.Units.torsionOrder`:
```lean
#check (NumberField.Units.torsionOrder K : ℕ)
```
:::

# The class group

::: leanSection
```lean -show
open NumberField
variable {K : Type*} [Field K] [NumberField K]
```
The *class group* measures the failure of {lean}`𝓞 K` to be a principal ideal domain.
In Lean this is {lean}`ClassGroup (𝓞 K)`:
```lean
#check (ClassGroup (𝓞 K) : Type _)
```
For a number field the class group is finite, this is one of the central finiteness
theorems of the subject, available as an instance:
```lean
example : Finite (ClassGroup (𝓞 K)) := inferInstance
```
Its cardinality is the *class number* {name}`NumberField.classNumber`, which is *defined*
as this cardinality:
```lean
example :
    classNumber K = Fintype.card (ClassGroup (𝓞 K)) := rfl
```
To produce elements of the class group from ideals, use {name}`ClassGroup.mk0`, which sends
a nonzero ideal to its class.
:::
