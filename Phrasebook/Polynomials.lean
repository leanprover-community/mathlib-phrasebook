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

#doc (Manual) "Polynomials" =>

This page explains how to express univariate and multivariate polynomials using the definitions in Mathlib.
We assume basic knowledge of both Lean and polynomials.
You can find a gentler introduction to polynomials in Mathlib in [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/C09_Groups_and_Rings.html#algebras-and-polynomials).
In addition to the material covered in that book, this chapter discusses:

* leading coefficients and monic polynomials
* coefficients and degree of multivariate polynomials

# The polynomial ring

::: leanSection
```lean -show
variable {R : Type*} [Semiring R]
```
The type of univariate polynomials with coefficients in a semiring `R` is {name}`Polynomial`.
To say "let `f` be a polynomial with coefficients in {lean}`R`", write:
```lean
variable (f : Polynomial R)
```

The notation `R[X]` for the polynomial ring over {lean}`R` is also available,
but it is *scoped* in the `Polynomial` namespace, so you have to open the scope to use it:
```lean
open scoped Polynomial

variable (g : R[X])
```
:::

In what follows we work over an arbitrary semiring unless stated otherwise.
It is common to open the entire `Polynomial` namespace,
so that the names {name}`Polynomial.C`, {name}`Polynomial.X`, {name}`Polynomial.monomial`,
{name}`Polynomial.eval`, {name}`Polynomial.natDegree` and {name}`Polynomial.degree`
(and many others) can be written without the `Polynomial` prefix.

## Constants and the indeterminate

::: leanSection
```lean -show
open scoped Polynomial
variable {R : Type*} [Semiring R] {r : R}
```
The *constant polynomials* are the image of the coefficient semiring {lean}`R`
in {lean}`R[X]`, embedded via the ring homomorphism {name}`Polynomial.C`:
```lean
#check (Polynomial.C r : R[X])
```
The indeterminate of the polynomial ring is {name}`Polynomial.X`:
```lean
#check (Polynomial.X : R[X])
```
Once the `Polynomial` namespace is open, you can write a polynomial as a Lean expression in `C` and `X`:
```lean
open Polynomial

#check (C r + C 2 * X ^ 2 + X ^ 3 : R[X])
```
:::

## Monomials

::: leanSection
```lean -show
open Polynomial
variable {R : Type*} [Semiring R] (r : R) (n : ℕ)
```
There is a dedicated constructor {name}`Polynomial.monomial` for a single term,
taking the degree and the coefficient:
```lean
#check (monomial 3 r : R[X])
```
The identity {name}`Polynomial.C_mul_X_pow_eq_monomial` translates between the two:
```lean
example : monomial 3 r = C r * X ^ 3 := by
  rw [C_mul_X_pow_eq_monomial]
```
Note that {lean}`(monomial n : R →ₗ[R] R[X])` is itself an {lean}`R`-linear map
sending a coefficient to the corresponding monomial of degree {lean}`n`,
rather than a plain function of two arguments.
This is occasionally relevant when applying lemmas about linear maps to it.

In practice, concrete polynomials are usually written as sums of terms of the form
{lean}`(C r * X ^ n : R[X])`, rather than as {lean}`(monomial n r : R[X])`:
the `C`/`X` form composes naturally under `+`, `*` and `^`,
and most arithmetic and coefficient lemmas are phrased against it.
The {name}`Polynomial.monomial` form is most useful when you want to manipulate
a single term abstractly, for instance to use its linearity in the coefficient.
:::

## Coefficients

::: leanSection
```lean -show
open Polynomial
variable {R : Type*} [Semiring R] (p : R[X]) (n : ℕ)
```
The coefficient of degree {lean}`n` of a polynomial {lean}`p` is {name}`Polynomial.coeff`,
written {lean}`p.coeff n`:
```lean
example : R := p.coeff n
```
The basic identities for `C`, `X` and `monomial` are {name}`Polynomial.coeff_C`,
{name}`Polynomial.coeff_X` and {name}`Polynomial.coeff_monomial`.
Two polynomials are equal iff all of their coefficients agree,
via {name}`Polynomial.coeff_inj` and the extensionality lemma {name}`Polynomial.ext`.

Coefficients of polynomials built from `C`, `X` and ring operations
can be computed term-by-term using {name}`Polynomial.coeff_add`,
{name}`Polynomial.coeff_C_mul`, {name}`Polynomial.coeff_X_pow`
(together with {name}`Polynomial.coeff_C` for constants).
For instance, the coefficients of `C r + C 2 * X ^ 2 + X ^ 3` are
`r, 0, 2, 1`, then `0` from degree `4` on:
```lean
example (r : R) :
    (C r + C 2 * X ^ 2 + X ^ 3 : R[X]).coeff 0 = r := by
  simp [coeff_add, coeff_X_pow, coeff_C]
example (r : R) :
    (C r + C 2 * X ^ 2 + X ^ 3 : R[X]).coeff 2 = 2 := by
  simp [coeff_add, coeff_C_mul, coeff_X_pow]
example (r : R) :
    (C r + C 2 * X ^ 2 + X ^ 3 : R[X]).coeff 3 = 1 := by
  simp [coeff_add, coeff_C_mul, coeff_X_pow]
```
:::

# Degree

## `natDegree` versus `degree`

::: leanSection
```lean -show
open Polynomial
variable {R : Type*} [Semiring R]
```
Mathlib provides two notions of degree, differing only in how they treat the zero polynomial:
```lean
#check (natDegree : R[X] → ℕ)
#check (degree : R[X] → WithBot ℕ)
```
For non-zero polynomials the two agree (via the coercion {lean}`((↑·) : ℕ → WithBot ℕ)`);
see {name}`Polynomial.degree_eq_natDegree`.
They differ at the zero polynomial: {name}`Polynomial.natDegree_zero` gives
{lean}`(0 : R[X]).natDegree = 0`, while {name}`Polynomial.degree_zero` gives
{lean}`(0 : R[X]).degree = ⊥`.

Many statements exist in both {name}`degree` and {name}`natDegree` form.
Sometimes, using {name}`degree` lets you deal uniformly with exceptions around the polynomial `0`.
Other times, viewing the polynomial `0` as a constant is exactly what is needed.
Another important distinction is that {name}`natDegree` takes values in {lean}`ℕ`,
where more tactics are likely to help close goals.

Coverage of both spellings is generally good, but in practice it varies lemma by lemma:
if the form you want is missing, look for it under the other name,
or use {name}`Polynomial.degree_eq_natDegree` to convert between them.

For computing or bounding the degree of a concrete polynomial built from `C`,
`X` and ring operations, the `compute_degree` tactic
(and its stronger variant `compute_degree!`) is often the easiest tool:
```lean
example : (X ^ 3 + C 2 * X + 1 : R[X]).natDegree ≤ 3 := by
  compute_degree
```
:::

## Leading coefficient and monic polynomials

::: leanSection
```lean -show
open Polynomial
variable {R : Type*} [Semiring R] (p : R[X])
```
The {name}`Polynomial.leadingCoeff` of {lean}`p` is its coefficient at degree {lean}`p.natDegree`:
```lean
example : R := p.leadingCoeff

example : p.leadingCoeff = p.coeff p.natDegree := rfl
```
A polynomial is *monic* if its leading coefficient is `1`.
The predicate is {name}`Polynomial.Monic`, defined as exactly this equality;
the named unfolding lemma is {name}`Polynomial.Monic.def`:
```lean
example : p.Monic ↔ p.leadingCoeff = 1 := Monic.def
```
Common building blocks include {name}`Polynomial.monic_one`, {name}`Polynomial.monic_X_add_C`
and {name}`Polynomial.monic_X_sub_C`, and {name}`Polynomial.Monic.mul`
shows that monicity is preserved by multiplication.
:::

# Evaluation

Evaluating a polynomial `p : R[X]` at an element translates into one of three
different definitions, depending on where the element lives:

* {name}`Polynomial.eval`: `p.eval r` when `r : R`;
* {name}`Polynomial.eval₂`: `p.eval₂ f a` when `a : A` and `f : R →+* A`,
  evaluating the polynomial in `A` after pushing its coefficients through `f`;
* {name}`Polynomial.aeval`: `p.aeval a` when `A` is an `R`-algebra and `a : A`.

These three are related: {name}`Polynomial.aeval_def` shows that `aeval`
is `eval₂` specialised to the `algebraMap`, and
{name}`Polynomial.eval_map` rewrites `eval₂` as an ordinary `eval`
after first {name}`Polynomial.map`-ping the coefficients.

## Evaluating at a ring element

::: leanSection
```lean -show
open Polynomial
variable {R : Type*} [Semiring R] (p : R[X]) (r : R)
```
For {lean}`p` of type {lean}`R[X]` and {lean}`r` of type {lean}`R`,
the value of {lean}`p` at {lean}`r` is {name}`Polynomial.eval`, written {lean}`p.eval r`:
```lean
example : R := p.eval r
```
:::

## Evaluating into an algebra

::: leanSection
```lean -show
open Polynomial
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (a : A)
```
When the coefficients live in a commutative semiring and we want to substitute
an element of an {lean}`R`-algebra {lean}`A` for `X`, use {name}`Polynomial.aeval`.
It is the algebra homomorphism extending the algebra map
{lean}`(algebraMap R A : R →+* A)` by sending `X` to a chosen element {lean}`a`:
```lean
#check (aeval a : R[X] →ₐ[R] A)
```
Use `aeval` (not `eval`) whenever the point of evaluation lives in a ring different
from the coefficient ring, for instance, evaluating a polynomial in `ℤ[X]` at a
real number, or at a matrix.
:::

# Roots

::: leanSection
```lean -show
open Polynomial
variable {R : Type*} [Semiring R] (p : R[X]) (r : R)
```
A point {lean}`r` is a *root* of {lean}`p` when {lean}`p.eval r = 0`.
This is recorded as {name}`Polynomial.IsRoot`, with named unfolding lemma
{name}`Polynomial.IsRoot.def`:
```lean
example : p.IsRoot r ↔ p.eval r = 0 := IsRoot.def
```
:::

## Multiset of roots in the coefficient ring

::: leanSection
```lean -show
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R] (p : R[X])
```
Over a commutative ring that is a domain, the multiset of roots of {lean}`p`,
counted with multiplicity, is {name}`Polynomial.roots`:
```lean
#check (p.roots : Multiset R)
```
By convention, {name}`Polynomial.roots_zero` says {lean}`((0 : R[X]).roots : Multiset R) = 0`
(the empty multiset), even though every element of {lean}`R` is a root of the zero
polynomial in the usual mathematical sense.
This convention keeps statements like {name}`Polynomial.roots_mul` clean.

The cardinality of `roots` is bounded by the degree:
see {name}`Polynomial.card_roots` and {name}`Polynomial.card_roots'`.
:::

## Roots in an extension

::: leanSection
```lean -show
open Polynomial
variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] (p : R[X])
```
When the roots of {lean}`(p : R[X])` should be sought in a (commutative-ring, domain)
`R`-algebra {lean}`S` rather than in {lean}`R` itself,
{name}`Polynomial.aroots` returns them as a {lean}`Multiset S`:
```lean
#check (p.aroots S : Multiset S)
```
The underlying set (without multiplicities) is {name}`Polynomial.rootSet`:
```lean
#check (p.rootSet S : Set S)
```
By definition, {name}`Polynomial.aroots` is the `roots` of `p.map (algebraMap R S)`,
and {name}`Polynomial.rootSet` is the coercion of that multiset to a set
(see {name}`Polynomial.aroots_def` and {name}`Polynomial.rootSet_def`).
:::

# Multivariate polynomials

::: leanSection
```lean -show
variable {σ R : Type*} [CommSemiring R] (i : σ)
```
For polynomials in several variables, use {name}`MvPolynomial`, parametrised by a type
{lean}`σ` of variables and a coefficient ring {lean}`R`:
```lean
#check (MvPolynomial σ R : Type _)
```
The variable indexed by an element {lean}`i` of {lean}`σ` is {lean}`(MvPolynomial.X i : MvPolynomial σ R)`,
and the constant embedding is {name}`MvPolynomial.C`.

Unlike the univariate case, where `R[X]` is a scoped notation in the
`Polynomial` namespace, Mathlib does *not* have notation for {lean}`MvPolynomial σ R`,
scoped or otherwise: you write {lean}`MvPolynomial σ R` directly,
even though docstrings and mathematical commentary throughout Mathlib often
use `R[σ]` or `R[X₁, …, Xₙ]` informally.
This notation is borrowed from the related types {lean}`AddMonoidAlgebra` and {lean}`MonoidAlgebra`, which do have scoped `R[M]` notation.
When a particular file uses the same multivariate polynomial ring repeatedly,
the usual workaround is a `local notation`.
For example, the Witt-vector files use `𝕄` to denote {lean}`MvPolynomial (Fin 2 × ℕ) ℤ`.

The type of variables {lean}`σ` can be chosen freely to fit the situation at hand,
and is unconstrained at the level of the definition itself.
When "finitely many variables" needs to be stated abstractly,
the usual idiom is to keep {lean}`σ` generic and add a {name}`Finite` or
{name}`Fintype` instance assumption on it as a separate hypothesis,
as is done for example in {name}`MvPolynomial.ringKrullDim_of_isNoetherianRing`.
The most common concrete choice in Mathlib is `Fin n`: this is what is used,
for example, to state results about finitely generated algebras in {name}`Algebra.FiniteType` and
{name}`Algebra.FinitePresentation`.
Other choices appear too: `Bool` is used internally in the construction of the
{name}`bernsteinPolynomial`, and `Bool × ℕ` shows up in the structure
polynomials behind {name}`WittVector`.
:::

## Coefficients, degree and evaluation

The core operations from the univariate setting have multivariate counterparts,
with the main difference that a "degree" is now a multidegree,
a function `σ →₀ ℕ` recording the exponent of each variable.

::: leanSection
```lean -show
variable {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R) (m : σ →₀ ℕ)
```
The coefficient of `p` at multidegree `m` is {name}`MvPolynomial.coeff`,
which takes a `σ →₀ ℕ` rather than a single natural number:
```lean
example : R := p.coeff m
```
Two multivariate polynomials are equal if and only if all coefficients agree
(see {name}`MvPolynomial.ext`).
:::

::: leanSection
```lean -show
variable {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R)
```
One notion of degree taking values in `ℕ` is the {name}`MvPolynomial.totalDegree`.
The `degree`/`natDegree` distinction from the univariate case has no analogue here.
```lean
#check (p.totalDegree : ℕ)
```
Per-variable degrees are also available via {name}`MvPolynomial.degreeOf`.
:::

::: leanSection
```lean -show
variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  (p : MvPolynomial σ R) (f : σ → R) (g : σ → A)
```
Evaluating a multivariate polynomial requires specifying a value for *each*
variable, given as a function indexed by `σ`.
The three flavours mirror the univariate case:

* {name}`MvPolynomial.eval`: `MvPolynomial.eval f p` when `f : σ → R`;
* {name}`MvPolynomial.eval₂`: like `eval`, but first pushing the coefficients
  through a ring homomorphism `R →+* A`;
* {name}`MvPolynomial.aeval`: `MvPolynomial.aeval g p` when `A` is an
  `R`-algebra and `g : σ → A`, the algebra homomorphism sending each
  variable `X i` to `g i`.

```lean
#check (MvPolynomial.eval f p : R)
#check (MvPolynomial.aeval g : MvPolynomial σ R →ₐ[R] A)
```
:::
