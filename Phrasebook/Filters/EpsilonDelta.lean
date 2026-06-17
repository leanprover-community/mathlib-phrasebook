/-
Copyright (c) 2026 The Mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mathlib community
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Phrasebook

set_option pp.rawOnError true

#doc (Manual) "ε-δ and filter bases" =>
%%%
tag := "filters-epsilon-delta"
%%%

```lean -show
open Filter Topology
```

Mathlib states limits and continuity in {name}`Tendsto` form, and you
should write your proofs that way too. This entry exists for a
narrow purpose: translating ε-δ statements you encounter in
textbooks or papers into filter form, so you can then close the
proof with the recipes in {ref "filters-proving"}[Proving limits]. Don't
reach for ε-δ inside Lean if you can avoid it; stay in filter-land.
({name}`Filter.HasBasis`, covered below, is a filter-native
generalisation and is fair game in filter-form proofs.)

# Continuity-style ε-δ for `𝓝 a`

::: leanSection
```lean -show
variable (f : ℝ → ℝ) (a L : ℝ)
```
For functions between metric spaces, the *unpunctured* ε-δ statement
translates to {lean}`Tendsto f (𝓝 a) (𝓝 L)`. The quantifier `∀ x` includes
`x = a`, so this is the continuity-style form (it forces `f a = L`):

```lean
example {f : ℝ → ℝ} {a L : ℝ} :
    Tendsto f (𝓝 a) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - L| < ε :=
  Metric.tendsto_nhds_nhds
```

This is *not* the punctured limit; for that, work in {lean}`𝓝[≠] a` (see
{ref "filters-punctured"}[Punctured vs unpunctured limits]).

Variants you'll reach for when the endpoints aren't both `𝓝 _`:

* {name}`Metric.tendsto_atTop`: source is {name}`atTop` (sequence limits in
  a metric space).
* {name}`Metric.tendsto_nhds`: target is `𝓝 _`, source is arbitrary.
:::

# Filter bases

You reach for {name}`Filter.HasBasis` in two situations: when you need an
ε-δ characterization that Mathlib does not already package as a named
lemma, and when you read a proof that unpacks a filter membership into
concrete witnesses. Both rest on the same *filter basis* pattern, of which
{name}`Metric.tendsto_nhds_nhds` is one instance. The neighbourhood filter
`𝓝 x` on a metric space *has basis* the open balls around `x`:

```lean
example {X : Type*} [PseudoMetricSpace X] (x : X) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) (Metric.ball x) :=
  Metric.nhds_basis_ball
```

::: leanSection
```lean -show
variable {X : Type*} [PseudoMetricSpace X] (l : Filter X) (p : X → Prop) (s : X → Set X)
variable (ε : ℝ) (x : X) (n : ℕ)
```
Read {lean}`HasBasis l p s` as: a set `t` is in `l` iff it contains some
`s i` with `p i`. The data `(p, s)` is a parametric ε-style
description of the filter. For `𝓝 x` on a metric space, the parameter
is `ε > 0` and the sets are the open balls {lean}`Metric.ball x ε`.

The two lemmas you'll reach for:

* {name}`Filter.HasBasis.mem_iff` turns `t ∈ l` into "there exists `i`
  with `p i` and `s i ⊆ t`". Use it to *unpack* a filter membership
  hypothesis.
* {name}`Filter.HasBasis.tendsto_iff` assembles a {name}`Tendsto` from a
  `(p, s)` basis on the source and a `(q, t)` basis on the target.
  This is the general ε-δ pattern, parametric in the basis.

Common bases:

* {name}`Metric.nhds_basis_ball`: `𝓝 x` has basis the open balls.
* {name}`Filter.atTop_basis`: {name}`atTop` has basis the sets {lean}`Set.Ici n`.

{name}`Metric.tendsto_nhds_nhds` and friends are derived from these via
{name}`HasBasis.tendsto_iff`.
:::
