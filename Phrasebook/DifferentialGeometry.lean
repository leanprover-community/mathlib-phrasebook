/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
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

set_option verso.code.warnLineLength 80

#doc (Manual) "Tutorial: How to do differential geometry using Mathlib" =>

This page explains how to express differential geometry using the definitions in Mathlib.
We assume basic knowledge of both Lean and differential geometry.

Recall that, intuitively, a smooth manifold is a topological space on which we can do calculus.
Formally, one commonly found definition is that an $n$-dimensional topological manifold is a topological space that is locally homeomorphic to an open ball in $n$-dimensional Euclidean space. (A smooth manifold imposes further conditions, which we will explain below.)

Mathlib's definition generalises this notion in three ways. Firstly, we also consider manifolds with boundary and corners --- the local model for a manifold can also be the upper half of an open ball, or a quadrant in such a ball.
Secondly, we allow manifolds over different fields: real manifolds are modelled on real Euclidean space, complex manifolds on a complex normed, but there are also manifolds over the `p`-adic numbers $`\mathbb{Q}_p`. In fact, a lot of manifold theory works over any {lean}`NontriviallyNormedField`, i.e. a normed field endowed with a norm which does not only take value zero or one.
Finally, manifolds need not be `n`-dimensional, but can also be infinite-dimensional --- i.e., modelled by open balls in any normed space (which need not be Banach), not just Euclidean space. Mathlib does not require manifolds to be Hausdorff nor second countable (though a number of theorems require this).

# Topological manifolds

Let's begin with topological manifolds. For topological manifolds, being modelled on some normed space generalises verbatim to any topological space, leading to the notion of `ChartedSpace`.

The following is how to state "let M be a topological manifold" in Lean.
```lean
variable {M H : Type*} [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]
```

An `n`-dimensional topological manifold (without boundary) is just a charted space on `n`-dimensional Euclidean space.
```lean
variable {M : Type*} {n : ℕ} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
```
For (real) manifolds with boundary (and no corners), the model is {lean}`EuclideanHalfSpace`.
```lean
variable {M : Type*} {n : ℕ} [NeZero n] [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
```
Note that such a manifold must have dimension at least one, hence the {lean}`NeZero n` hypothesis.

Taking products of manifolds with boundary yields manifolds with corners; mathlib allows corners of any order. They can be modelled by on a {lean}`EuclideanQuadrant`. The following defines a real `n`-dimensional real manifold, potentially with corners of all orders.
```lean
variable {M : Type*} {n : ℕ} [NeZero n] [TopologicalSpace M]
  [ChartedSpace (EuclideanQuadrant n) M]
```

A charted space has a corresponding *atlas*, containing a coordinate chart at each point.
In Lean, every point has a distinguished chart ("the preferred chart" at that point).
```lean
variable {M H : Type*} [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

-- Here's how to access the atlas.
#check atlas H M

-- The preferred chart at x.
variable {x : M} in
#check chartAt H x
```

The astute reader may notice there is no difference between topological manifolds with corners and boundary. For smooth manifolds, the situation is different.

# Smooth manifolds

The textbook definition of smooth manifolds is "a topological manifold such that all coordinate changes are smooth".
Making sense of this for manifolds with boundary or corners requires thinking: naively, one would obtain coordinate changes which are defined on *topological spaces* (such as, Euclidean quadrants) --- whereas smoothness requires a normed space.
For Euclidean quadrants, there is a natural candidate: embed a Euclidean quadrant into its corresponding Euclidean space. (This corresponds to defining a map on Euclidean quadrants as smooth if it admits a smooth extension to the full space.)
For general manifolds, such an embedding is encoded in a {lean}`ModelWithCorners`; smoothness is defined in terms of the resulting map after composition with the model with corners.
A `ModelWithCorners` takes three parameters: the base field `k` in which we're working, a `k`-normed space and a topological space on which the manifold is modelled.
Finally, `IsManifold` encodes that `M` is a smooth manifold, w.r.t. a specified model with corners. Here is how to say "let `M` be a $`C^k` manifold" (for $`k\in\mathbb{N}`).
```lean
variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] {k : ℕ}
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I k M]
```
For manifolds without boundary, there is a natural model with corners (taking the identity map on the model normed space), which has special notation.
```lean
open scoped Manifold
variable {𝕜 E M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {k : ℕ}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) k M]
```

The parameter `k` can be a natural number, `∞` for smooth manifolds, and `ω` for analytic manifolds (whose coordinate changes are analytic). To allow $`k=∞` (smooth manifolds) or analytic manifolds, take `k` in the type `ℕ∞ω` (which is notation for {lean}`WithTop ENat`).
```lean
open scoped ContDiff
variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] {k : ℕ∞ω}
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I k M]
```
For smooth manifolds, we can use the notation `∞` in the `ContDiff` namespace.
```lean
open scoped ContDiff
variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I ∞ M]
```
For analytic manifolds, we can use the notation `ω` in the `ContDiff` namespace.
```lean
open scoped ContDiff
variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I ω M]
```

For a real manifold, we can drop the parameter `𝕜` (and just speak about `ℝ` instead).
```lean
open scoped ContDiff
variable {E M H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] {k : ℕ∞ω}
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I k M]
```

Atlasses are not maximal in general --- but there a maximal atlas, consisting of all charts which are compatible with a given smooth structure, induced by a model with corners.
```lean
open scoped ContDiff
variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] {k : ℕ∞ω}
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I k M]

#check IsManifold.maximalAtlas I n M
```

A smooth manifold with boundary decomposes into interior and boundary points. {name}`ModelWithCorners.IsInteriorPoint` denotes `x : M` being an interior point (w.r.t. the model `I`), `ModelWithCorners.IsBoundaryPoint` describes points which lie on the boundary (or some corner).

There are two kinds of manifolds without boundary.
If a model with corners has full range (i.e., the embedding `H → E` of the model space into a normed space is surjective), there can be no boundary points: this is `ModelWithCorners.Boundaryless`.
A more general condition (which is harder to check) is "every point is an interior point".
```lean
#check BoundarylessManifold
```
Mathlib knows about the interior and boundary of product manifolds, for example:
```lean
#check ModelWithCorners.interior_prod
```
There is a definition of "manifolds whose boundary is smooth" (i.e., there are no corners), which is not in mathlib yet.

# Differentiability

Let `M` and `N` be smooth manifolds, over the same field (but with potentially different models with corners).
We define differentiability and continuous differentiability in local charts.
In particular, this depends on our chosen models with corners.
:::leanSection
```lean
set_option linter.unusedVariables false -- used later in this section
open scoped ContDiff
variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] {k : ℕ∞ω}
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I k M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners 𝕜 E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {s : Set M} {x : M}
```

This is how to state "f is $`C^n`", "f is $`C^n` on `s`" and "f is $`C^n` at `x`" (and the analogous statements about differentiability), respectively.
```lean
#check ContMDiff I J n f
#check ContMDiffOn I J n f s
#check ContMDiffAt I J n f x
#check MDifferentiable I J f
#check MDifferentiableOn I J f s
#check MDifferentiableAt I J f x
```
In many cases, the model of corners is somewhat obvious from context: in our setting, there is only a single model on `M`, for example (namely `I`). There is special notation to allow omitting the model with corners in most cases. The following is equivalent to the previous block, but shorter.

```lean
#check CMDiff n f
#check CMDiff[s] n f
#check CMDiffAt n f x
#check MDiff f
#check MDiff[s] f
#check MDiffAt f x
```
To complete the picture, mathlib also has a definition for being $`C^n` (resp. differentiable) at a point within a set, called {lean}`ContMDiffWithinAt I J n f s x` (with notation {lean}`CMDiffAt[s] n f x`) and {lean}`MDifferentiableWithinAt I J f s x` (with notation {lean}`MDiffAt[s] f x`), respectively.

The differential of a smooth map is called {name}`mfderiv`, the manifold version of the Fréchet derivative {lean}`fderiv`.
```lean
#check mfderiv I J f x
#check mfderiv% f x -- equivalent notation

```
Its design uses a junk value pattern: even if `f` is not differentiable at `x`, its `mfderiv` is defined (as zero).
This avoids having to specify differentiability hypotheses all the time, but also implies a little caution is needed when interpreting statements: `mfderiv I J f x = 0` does not imply that `f` is differentiable! The notion {name}`HasMFDerivAt` states that `f` is differentiable at a given point, with given differential.
```lean
variable {f' : TangentSpace I x →L[𝕜] TangentSpace J (f x)}
#check HasMFDerivAt I J f x f'
#check HasMFDerivAt% f x f' -- equivalent notation
```
There are also versions of this concept within a set:
```lean
variable {f' : TangentSpace I x →L[𝕜] TangentSpace J (f x)}
#check mfderivWithin I J f s x
#check mfderiv[s] f x -- equivalent notation
#check HasMFDerivWithinAt I J f s x f'
#check HasMFDerivAt[s] f x f' -- equivalent notation
```
:::

# Constructions and explicit examples of manifolds

Lean knows about various constructions and examples of manifolds.
:::leanSection
```lean
open scoped ContDiff Manifold
variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] {k : ℕ∞ω}
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I k M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners 𝕜 E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J k N]
```

```lean
-- The product of two `C^k` manifolds `M` and `N` is a `C^k` manifold.
example : IsManifold  (I.prod J) k (M × N) := inferInstance

-- The disjoint union of two `C^k` manifolds over the same model with corners
-- is a `C^k` manifold.
example {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I k M'] :
  IsManifold I k (M ⊕ M') := inferInstance

-- A normed space is a smooth manifold (modelled on itself).
#synth IsManifold 𝓘(𝕜, E) ∞ E
```
:::

```lean
open Metric Module in
/- The sphere in a finite-dimensional inner product space is a smooth manifold -/
example (n : ℕ) (E : Type*) [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)] :
  IsManifold (𝓡 n) ω (sphere (0 : E) 1) := inferInstance

#check contMDiff_coe_sphere
open Metric Module in
/- The map 𝕊ⁿ ↪ ℝⁿ⁺¹ is smooth -/
example {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)] :
  CMDiff ⊤ (fun x ↦ x : sphere (0 : E) 1 → E) := contMDiff_coe_sphere

-- The group of units in any Banach space is a smooth manifold
-- (in fact, even a Lie group).
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
  (n : ℕ∞ω) : IsManifold 𝓘(𝕜, V →L[𝕜] V) n (V →L[𝕜] V)ˣ := inferInstance

-- A non-trivial closed real interval is a manifold.
example (x y : ℝ) [Fact (x < y)] {n : ℕ∞ω} :
  IsManifold (𝓡∂ 1) n (Set.Icc x y) := inferInstance

/- The circle is a Lie group -/
example : LieGroup (𝓡 1) ⊤ Circle := inferInstance


-- Quotient manifolds will be merged into mathlib soon.
```
