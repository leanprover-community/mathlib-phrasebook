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

#doc (Manual) "Bridges to ε-δ and filter bases" =>

Mathlib states limits and continuity in `Tendsto` form, but the proofs
you write often start from ε-δ data. This entry covers the
translation in both directions: the metric-space bridge lemmas and the
{name}`Filter.HasBasis` API that generalises them.

# Continuity-style ε-δ for `𝓝 a`

For functions between metric spaces, `Tendsto f (𝓝 a) (𝓝 L)` unfolds
to the **unpunctured** ε-δ statement — the quantifier `∀ x` includes
`x = a`, so this is the continuity-style form (it forces `f a = L`):

::: leanSection
```lean -show
open Filter Topology
```
```lean
example {f : ℝ → ℝ} {a L : ℝ} :
    Tendsto f (𝓝 a) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - L| < ε :=
  Metric.tendsto_nhds_nhds
```
:::

This is *not* the classical deleted-neighbourhood limit; for that,
work in `𝓝[≠] a` (see "Punctured vs unpunctured" in *Limit
statements*).

Variants you'll reach for:

* {name}`Metric.tendsto_nhds_nhds` — both endpoints are `𝓝 _`
  (function limits at a point, continuity-style).
* {name}`Metric.tendsto_atTop` — source is `atTop` (sequence limits in
  a metric space).
* {name}`Metric.tendsto_nhds` — target is `𝓝 _`, source is arbitrary.

# Filter bases

The metric-space bridge above is one instance of a general pattern.
The neighbourhood filter `𝓝 x` on a metric space *has basis* the
open balls around `x`:

::: leanSection
```lean -show
open Filter Topology
```
```lean
example {X : Type*} [PseudoMetricSpace X] (x : X) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) (Metric.ball x) :=
  Metric.nhds_basis_ball
```
:::

Read `HasBasis l p s` as: a set `t` is in `l` iff it contains some
`s i` with `p i`. The data `(p, s)` is a parametric ε-style description
of the filter — for `𝓝 x` on a metric space, the parameter is
`ε > 0` and the sets are the open balls `Metric.ball x ε`.

The two lemmas you'll reach for:

* {name}`Filter.HasBasis.mem_iff` — *use* a filter: turn `t ∈ l` into
  "there exists `i` with `p i` and `s i ⊆ t`".
* {name}`Filter.HasBasis.tendsto_iff` — *prove* a `Tendsto`: assemble
  it from a `(p, s)` basis on the source and a `(q, t)` basis on the
  target. This is the general ε-δ pattern, parametric in the basis.

Common bases:

* {name}`Metric.nhds_basis_ball` — `𝓝 x` has basis the open balls.
* {name}`Filter.atTop_basis` — `atTop` has basis the sets `Set.Ici n`.

`Metric.tendsto_nhds_nhds` and friends are derived from these via
`HasBasis.tendsto_iff`.

