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

# Turning a `Tendsto` into ε-δ (and back)

For functions between metric spaces, `Tendsto` unfolds to a familiar
ε-δ statement:

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

Variants you'll reach for:

* {name}`Metric.tendsto_nhds_nhds` — both endpoints are `𝓝 _`
  (function limits at a point in a metric space).
* {name}`Metric.tendsto_atTop` — source is `atTop` (sequence limits in
  a metric space).
* {name}`Metric.tendsto_nhds` — target is `𝓝 _`, source is arbitrary.

# Filter bases

To work with a concrete description of an arbitrary filter, use
{name}`Filter.HasBasis`: a filter `l` *has basis* `(p, s)` iff its
members are exactly the supersets of `s i` for some `i` with `p i`.
Two key lemmas:

* {name}`Filter.HasBasis.mem_iff` — *use* a filter: extract a witness
  `i` (with `p i`) from a membership hypothesis.
* {name}`Filter.HasBasis.tendsto_iff` — *prove* a `Tendsto`: assemble
  it from a `(p, s)` basis on the source and a `(q, t)` basis on the
  target. This is the general "ε-δ" pattern, parametric in the basis.

Common bases:

* {name}`Metric.nhds_basis_ball` — neighbourhoods of `x` have basis
  the open balls around `x`.
* {name}`Filter.atTop_basis` — `atTop` has basis the sets `Set.Ici n`.

The metric-space bridge lemmas (`Metric.tendsto_nhds_nhds` and
friends) are derived from these via `HasBasis.tendsto_iff` applied to
`Metric.nhds_basis_ball` and/or `Filter.atTop_basis`.

# Gotcha: punctured vs unpunctured

`Tendsto f (𝓝 a) (𝓝 L)` includes the behaviour of `f` *at* `a` — if
`f a ≠ L`, you cannot have this. For the classical "limit as `x → a`
with `x ≠ a`", use the punctured neighbourhood filter `𝓝[≠] a`:

::: leanSection
```lean -show
open Filter Topology
```
```lean
example (f : ℝ → ℝ) (a L : ℝ) :
    Prop := Tendsto f (𝓝[≠] a) (𝓝 L)
```
:::

The standard ε-δ definition of "limit at a point" without continuity
corresponds to `𝓝[≠] a`, not `𝓝 a`; Mathlib's
{name}`Metric.tendsto_nhds_nhds` covers the unpunctured (continuity)
case.
