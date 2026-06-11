/-
Copyright (c) 2026 The Mathlib Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mathlib community
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

import Phrasebook.Filters.Tendsto
import Phrasebook.Filters.Proving
import Phrasebook.Filters.EpsilonDelta
import Phrasebook.Filters.Operations

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Phrasebook

set_option pp.rawOnError true

#doc (Manual) "How to work with filters in Mathlib" =>

Mathlib states every limit, "eventually", and "almost everywhere" claim
through *filters*. If you want to write `lim_{x → 0} sin x / x = 1` as a
Lean proposition, prove that a sequence converges, or read a proof that
pivots through `𝓝` and `atTop`, this chapter shows how. It assumes you are
comfortable with Lean and with limits in the usual ε-δ sense, but not that
you have met filters before.

::: leanSection
```lean -show
open Filter Topology MeasureTheory
variable {α : Type*} {l : Filter α} {s : Set α}
variable {X : Type*} [TopologicalSpace X] {x : X}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
```
A {name}`Filter` `l` on a type `α` packages a notion of "eventually": for a
set `s : Set α`, membership {lean}`s ∈ l` reads "we *eventually* land in
`s`". Different filters carry different notions: {lean}`𝓝 x` is "for points
near `x`", `atTop` is "for sufficiently large input", {lean}`ae μ` is "for
almost every point". You rarely touch the axioms directly; the skill is
picking the filter that matches the limit you mean and letting the lemmas do
the work. One relation, {name}`Filter.Tendsto`, then covers sequence
convergence, function limits at a point, "→ ∞", and almost-everywhere
statements uniformly.
:::

# The standard filters

::: table +header

* * Filter
  * Lives on
  * "Eventually in this filter" means

* * `𝓝 x`
  * a {name}`TopologicalSpace`
  * near the point `x`

* * `𝓝[s] x`
  * within a subset
  * near `x`, restricted to `s`

* * `𝓝[>] x`, `𝓝[<] x`
  * an order topology
  * from the right/left of `x`

* * {name}`Filter.atTop`
  * a {name}`Preorder`
  * for sufficiently large input

* * {name}`Filter.atBot`
  * a {name}`Preorder`
  * for sufficiently small input

* * {name}`Filter.cofinite`
  * any type
  * for all but finitely many points

* * `μ.ae`
  * a measure space
  * for almost every point

* * {name}`Filter.principal` `s`
  * any
  * exactly inside `s`

* * `⊤`
  * any
  * everywhere (only `Set.univ` is in `⊤`)

* * `⊥`
  * any
  * vacuously (every set is in `⊥`; see the gotcha in
    {ref "filters-tendsto"}[Limit statements])

:::

The chapter has four entries:

* {ref "filters-tendsto"}[Limit statements] — turn a mathematical limit into
  a Mathlib proposition.
* {ref "filters-proving"}[Proving limits] — prove such a statement once it is
  written.
* {ref "filters-epsilon-delta"}[ε-δ and filter bases] — translate textbook
  ε-δ statements into filter form.
* {ref "filters-operations"}[Operations on filters] — read the `≤`,
  `Filter.map`, `Filter.comap`, and `Filter.prod` algebra in other people's
  proofs.

The notations `𝓝`, `atTop`, `∀ᶠ` only parse after `open Filter Topology`.

{include 1 Phrasebook.Filters.Tendsto}

{include 1 Phrasebook.Filters.Proving}

{include 1 Phrasebook.Filters.EpsilonDelta}

{include 1 Phrasebook.Filters.Operations}
