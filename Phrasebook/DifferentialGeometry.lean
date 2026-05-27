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

The astute reader may notice there is no difference between topological manifolds with corners and boundary. For smooth manifolds, the situation is different.

# Smooth manifolds

xxx all of this is explanation, not how to
A topological manifold is smooth if it has a smooth atlas, i.e. an atlas of coordinate charts whose coordinate changes are smooth maps. If `M` is a smooth manifold with boundary, expressing "this coordinate change is smooth" would naively be a statement about smoothness of a map between subsets of a normed space. The easiest way to define this is by extension.
We encode this in a model with corners. (XXX terrible explanation!)

Mathlib encodes this concept in a `ModelWithCorners`, encoding the base field (to distinguish e.g. real and complex manifolds: every complex manifold is also a real manifold, but the resulting notions of smoothness are different --- for instance, a one-dimensional complex differentiable manifold is in fact analytic!), the topological space your manifold is modelled on and the underlying normed space.

Smoothness parameter: natural number, ∞ for smooth manifolds or ω for analytic

Lean's theory of manifolds is very general, and also includes manifoldsallows manifolds


Lean's manifold library includes manifolds over the real, complex numbers and `p`-adic numbers:
the notion of `NontriviallyNormedField` encapsulates all we need, and notably includes these three cases.
Here is how to say "let `M` be a $`C^k` manifold" (for $`k\in\mathbb{N}`).
```
variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] {k : ℕ}
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I k M]
```
To allow $`k=∞` (smooth manifolds) or analytic manifolds, take `k` in the type `ℕ∞ω` (which is notation for {lean}`WithTop ENat`).
```
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

Differentiability of maps between manifolds is stated with respect to models with corners on the domain and co-domain.
:::leanSection
```lean
open scoped ContDiff
variable {E M H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] {k : ℕ∞ω}
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I k M]
```

-- second manifold and all the definitions we wanted
:::
