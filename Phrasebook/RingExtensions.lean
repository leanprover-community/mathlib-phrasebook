/-
Copyright (c) 2026 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


open Phrasebook

set_option pp.rawOnError true

#doc (Manual) "Ring extensions" =>
%%%
tag := "ring extensions"
%%%

```lean -show
variable {R S T K : Type*} [CommRing R] [CommRing S] [CommRing T] [DivisionRing K]
```

This page explains how to write a tower of ring extensions in Mathlib.
We assume that you have read [Mathematics in Lean chapter 9 on Groups and Rings](https://leanprover-community.github.io/mathematics_in_lean/C09_Groups_and_Rings.html).
We will explain how Mathlib represents the following sentence:
"Let {lean}`R`, {lean}`S` and {lean}`T` be commutative rings, such that {lean}`R` is included in {lean}`S` and {lean}`S` is included in {lean}`T`."
Although we focus on commutative rings for simplicity, everything holds unless mentioned otherwise for semirings and fields.
See {ref "generalized ring extensions"}[The non-unital, non-associative case] for info on generalizing the assumptions further.

# Algebras

:::leanSection
```lean -show
variable [Algebra R S]
```

Mathlib represents inclusions of rings uniformly using the class {name}`Algebra`.
Specifically, `[Algebra R S]` supplies a canonical homomorphism from {lean}`R` to {lean}`S`: {lean}`algebraMap R S`.
The idea then is that we set up the instances so that an extension of rings $`S / R` becomes represented by the inclusion map {lean}`algebraMap R S`.
Mathlib provides many of these inclusion maps already

Algebra instances in Mathlib include:

```lean
#check algebraMap ℕ R -- n ↦ 1 + ... + 1, `n` times
#check algebraMap ℤ R -- ± n ↦ ± (1 + ... + 1), `n` times
variable [CharZero K] in
#check algebraMap ℚ K -- ± n ↦ ± (1 + ... + 1), `n` times

#check algebraMap R R -- x ↦ x

#check algebraMap R (Polynomial R) -- x ↦ C x

variable (s : Subring R) in
#check algebraMap s R -- ⟨x, hx⟩ ↦ x

variable (s : Submonoid R) in
#check algebraMap R (Localization s) -- x ↦ x/1
```
:::

## Injectivity

:::leanSection
```lean -show
variable [Algebra R S]
```

An {name}`algebraMap` is not necessarily injective: it can be any ring homomorphism in principle.
For ring extensions, you might need to add an extra hypothesis
saying {lean}`Function.Injective (algebraMap R S)`.
Many of the theorems on ring extensions do not need these hypotheses, however,
and in many other cases {lean}`algebraMap R S` is already true:
for example when {lean}`R` is a division ring (see {name}`RingHom.injective`)
or {lean}`R` is the natural numbers or the integers and {lean}`S` has characteristic 0.

:::

# Towers of extensions

:::leanSection
When we have a tower of ring extensions, $`T / S / R`, there are three inclusion maps:
$`R \to S`, $`S \to T` and $`R \to T`. Those correspond to three {name}`Algebra` instances:
```lean
variable [Algebra R S] [Algebra S T] [Algebra R T]
```
We then need to ensure the inclusion maps commute, for which we use the {name}`IsScalarTower` class:
```lean
variable [IsScalarTower R S T]

example : algebraMap R T =
    (algebraMap S T).comp (algebraMap R S) :=
  IsScalarTower.algebraMap_eq R S T
```

Note that only having {lean}`Algebra R S` and {lean}`Algebra S T` instances is not enough to allow
Lean to infer {lean}`Algebra R T`: the typeclass system cannot guess a value for {lean}`S`.
If the {lean}`Algebra R T` instance is missing, you could declare it as:
```lean
example : Algebra R T :=
  Algebra.compHom T (algebraMap R S)
```
But a more specialized implementation is often better for definitional equality.


```lean -show
variable {K L : Type*} [Field K] [DivisionRing L] [Algebra K L]
```

Mathlib has a variety of scalar tower instances. For example:
```lean
#synth IsScalarTower ℕ R S -- where `[Algebra R S]`
#synth IsScalarTower ℤ R S -- where `[Algebra R S]`
variable [CharZero K] [CharZero L] in
#synth IsScalarTower ℚ K L -- where `[Algebra K L]`

#synth IsScalarTower R R S
#synth IsScalarTower R S S

#synth IsScalarTower R S (Polynomial S)

variable (s : Subring R) in
#synth IsScalarTower s R S

variable (s : Submonoid S) in
#synth IsScalarTower R S (Localization s)
```

:::

# Subrings

Another way to represent ring extensions is with subrings.
The main drawback of using subrings everywhere is
viewing an existing ring as a subring of another requires transferring existing results.
Moreover, there is no obvious "universal" ring
we can choose for Mathlib to include every other ring as a subring.
Still, Mathlib has tools to move between {name}`Algebra` and {name}`Subring`.

As mentioned above, a subring $`s \le R` has an automatic {name}`Algebra` instance:
```lean
variable (s : Subring R)
#synth Algebra s R
```
Moreover, if we have an extension $`S / R`, the expected {name}`IsScalarTower` instance is found automatically:
```lean
variable [Algebra R S]
#synth IsScalarTower s R S
```

:::leanSection

Suppose we are given an inclusion of subrings:
```lean
variable {s t : Subring R} (h : s ≤ t)
```

Then we have to create the {name}`Algebra` and {name}`IsScalarTower` instances ourselves:
```lean
abbrev inclusionAlgebra : Algebra s t :=
  RingHom.toAlgebra (Subring.inclusion h)

instance : letI := inclusionAlgebra h;
    IsScalarTower s t R :=
  let := inclusionAlgebra h
  { smul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ z ↦ smul_assoc x y z }
```

The other option is to turn {lean}`s` into a subring of {lean}`t`, as {lean}`s.comap t.subtype`:
```lean
#synth IsScalarTower (s.comap t.subtype) t R
```
When working pointwise this gets messy fast though,
mapping between elements of {lean}`s` and the corresponding elements of {lean}`s.comap t.subtype`.

:::

# The non-unital, non-associative case
%%%
tag := "generalized ring extensions"
%%%

Since {lean}`Algebra R S` assumes {lean}`R` is a commutative semiring and {lean}`S` is a semiring,
in the non-unital and/or non-associative case
we need to replace the assumption `[Algebra R S]` with `[Module R S] [SMulCommClass R S S] [IsScalarTower R S S]`.
Note that we lose access to {name}`algebraMap`, so working with non-unital, non-associative ring extensions requires explicitly passing around the maps.

Given an {lean}`Algebra R S` instance, the instances for {lean}`Module R S`, {lean}`SMulCommClass R S S` and {lean}`IsScalarTower R S S` can be automatically inferred.
The converse cannot be done using the typeclass system but can be added manually, using {lean}`Algebra.ofModule (R := R) (A := S) smul_mul_assoc mul_smul_comm`.
Mathlib always uses {name}`Algebra` in the unital, associative case.
