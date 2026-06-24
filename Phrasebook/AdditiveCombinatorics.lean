/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import AddCombi
import Mathlib
import Phrasebook.Meta.Lean
import VersoManual

open Phrasebook
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Additive combinatorics" =>

This page explains how to express common concepts in additive combinatorics
using the definitions in Mathlib and [AddCombi](https://github.com/leanprover-community/add-combi).
We assume basic knowledge of both Lean and additive combinatorics.

# Sets

## Sets and finite sets

The basic objects of study in additive combinatorics are "additive sets", i.e. sets in a group.
Sets in Mathlib live on a single type. Here is how to declare a subset of an abelian group:
```lean
variable {G : Type*} [AddCommGroup G] {A : Set G}
```

Finite sets can be represented in two ways. Either we work with sets that happen to be finite:
```lean
variable {A : Set G} (hA : A.Finite)
```
or we work with bundled finite sets
```lean
variable {A : Finset G}
```
The latter is preferred in Mathlib since it gives access to e.g. {name}`Finset.sum`.

In finite groups, all sets are finite and therefore all sets happen to be finite.
We tend to prefer working with {name}`Finset` anyway to access its API.

The cardinality of a {name}`Set` is {name}`Set.ncard`:
```lean (name := setNCard)
variable {A : Set G}

#check A.ncard
```
```leanOutput setNCard
A.ncard : ℕ
```
Similarly, the cardinality of a {name}`Finset` is {name}`Finset.card`.
We provide the usual cardinality notation for it:
```lean (name := finsetCard)
variable {A : Finset G}

open scoped Finset

#check #A
```
```leanOutput finsetCard
#A : ℕ
```

## Indicators

```lean -show
variable {R : Type*} [Zero R] [One R] {A : Set G}
```
The {lean}`R`-valued indicator function of {lean}`(A : Set G)` is written as
```lean (name := indicator)
variable {R : Type*} [Zero R] [One R] {A : Set G}

#check A.indicator (1 : G → R)
```
```leanOutput indicator
A.indicator 1 : G → R
```
AddCombi provides convenient notation:
```lean (name := indicatorNotation)
open scoped Indicator

#check 𝟭_[A, R]
```
```leanOutput indicatorNotation
𝟭_[A, R] : G → R
```
When no return type is specified, the notation defaults to the {lean}`ℕ`-valued indicator.
```lean (name := indicatorNotation)
#check 𝟭_[A]
```
```leanOutput indicatorNotation
𝟭_[A] : G → ℕ
```

```lean -show
variable {A : Finset G} {g : G}
```
When talking about the indicator function of a {name}`Finset`,
you might need to help Lean somewhat using a type ascription.
In the following, {lean}`g` has type {lean}`G`, so Lean coerces {lean}`A` to {lean}`Set G`.
```lean
variable {A : Finset G} {g : G}

#check 𝟭_[A] g
```
Without such unification information, a type ascription is required.
```lean
#check 𝟭_[(A : Set G)]
```

## Sumsets

Sumsets and product sets in an (additive) monoid enjoy the usual arithmetic notation,
once the `Pointwise` scope is opened:
```lean (name := sumset)
variable {A B : Set ℕ}

open scoped Pointwise

#check A + B
#check A * B
```
```leanOutput sumset
A + B : Set ℕ
```
```leanOutput sumset
A * B : Set ℕ
```
Similarly, the notations for repeated sumsets and product sets is simply
```lean (name := repeatedSumset)
variable {n : ℕ}

#check n • A
#check A ^ n
```
```leanOutput repeatedSumset
n • A : Set ℕ
```
```leanOutput repeatedSumset
A ^ n : Set ℕ
```
Careful! In additive combinatorics one also encounters the "dilate set",
where each element of the set is multiplied by a fixed natural number.
We currently do not provide a way to write this operation conveniently.
Dilation by anything other than a natural number uses
the standard scalar multiplication notation:
```lean (name := dilateSet)
variable {A : Set ℝ} {q : ℚ}

#check q • A
```
```leanOutput dilateSet
q • A : Set ℝ
```
```lean -show
variable {G₀ : Type*} [GroupWithZero G₀]

#check q • A
```
Sets can also be pointwise negated or inverted
(with the usual convention that {lean}`(0 : Set G₀)⁻¹ = 0`):
```lean (name := inverseSet)
#check A⁻¹
#check -A
```
```leanOutput inverseSet
A⁻¹ : Set ℝ
```
```leanOutput inverseSet
-A : Set ℝ
```
Finally, {name}`Finset` is equipped with the same operations
_under the further assumption that the group has decidable equality_:
```lean (name := sumFinset)
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
  {A B : Finset G}

#check A + B
```
```leanOutput sumFinset
A + B : Finset G
```
This extra assumption allows us to perform computations with {name}`Finset`:
```lean (name := computeSumset)
#eval ({1, 2} + {4, 7} : Finset ℕ)
```
```leanOutput computeSumset
{5, 8, 6, 9}
```

# Quantities

## Doubling constant

```lean -show
variable {K : ℝ}
```
The easiest way to talk about a {name}`Finset` having doubling at most {lean}`K` is simply
```lean
open scoped Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
  {K : ℝ} {A : Finset G} (hA : #(A + A) ≤ K * #A)
```
and similarly for small difference.
One can also write the doubling and difference constants {name}`Finset.addConst` and
{name}`Finset.subConst` directly as follows:
```lean (name := doubling)
open scoped Combinatorics.Additive

#check σ[A]
#check δ[A]
```
```leanOutput doubling
σ[A] : ℚ≥0
```
```leanOutput doubling
δ[A] : ℚ≥0
```
```lean -show
variable [Group G]
```
The multiplicative doubling and difference constants {name}`Finset.mulConst` and
{name}`Finset.divConst` are denote {lean}`σₘ[A]` and {lean}`δₘ[A]`.

One can relate {lean}`σ[A] ≤ K` and {lean}`#(A + A) ≤ K * #A` through
{name}`Finset.addConst_mul_card`.

Mathlib contains the proof of the Ruzsa triangle and Plünnecke-Ruzsa inequalities.
See {name}`Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub`.

## Energy

The energy of a {name}`Finset` is {name}`Finset.addEnergy`:
```lean (name := energy)
variable {A : Finset G}

open scoped Combinatorics.Additive

#check E[A]
```
Similarly to the doubling constant, the multiplicative energy {name}`Finset.mulEnergy`
is denoted {lean}`Eₘ[A]`.

Mathlib knows that sets of small doubling have large energy
(see {name}`Finset.le_card_add_mul_addEnergy`), and AddCombi knows the partial converse,
namely the Balog-Szemerédi-Gowers theorem (see {name}`BSG`).

## Covering

To say that a set {lean}`B` is covered by {lean}`K` translates of another set {lean}`A`,
one can use the predicate {name}`CovByVAdd` (or its multiplicative version {name}`CovBySMul`):
```lean
variable {A B : Set G} {K : ℝ} (hAB : CovByVAdd G K A B)
```

This is in turn used to define approximate subgroups:
```lean
variable (hA : IsApproximateAddSubgroup K A)
```

# The future

## Fourier analysis

There is currently no support for Fourier analysis on finite (abelian) groups in Mathlib.

## Compact groups

There is currently no support for additive combinatorics on compact (abelian) groups in Mathlib.
