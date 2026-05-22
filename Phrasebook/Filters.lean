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

#doc (Manual) "Filters" =>

A *filter* on `α` is Mathlib's universal device for talking about
"limiting behaviour". A single definition — {name}`Filter` — encodes
neighbourhoods of a point, "x → ∞", almost-everywhere statements,
convergence along a subsequence, and "all but finitely many points";
a single relation — {name}`Filter.Tendsto` — covers every limit you
would otherwise have to redefine.

The intuition: `s ∈ l` reads "we *eventually* end up in `s`". For
`𝓝 x` that's "for points sufficiently near `x`"; for `atTop` on `ℕ`,
"for sufficiently large `n`"; for `μ.ae`, "for almost every point";
for `cofinite`, "for all but finitely many". The filter axioms —
`univ ∈ l`, upward-closed, closed under finite intersection — just
say "eventually" is preserved by supersets and by conjunction.

# The standard filters

::: table +header

* * Filter
  * Lives on
  * "Eventually in this filter" means

* * `𝓝 x` (= {name}`nhds`)
  * a {name}`TopologicalSpace`
  * near the point `x`

* * `𝓝[s] x` (= {name}`nhdsWithin`)
  * within a subset
  * near `x`, restricted to `s`

* * `𝓝[>] x`, `𝓝[<] x`
  * an order topology
  * from the right/left of `x`

* * {name}`Filter.atTop`
  * a {name}`Preorder` with no top
  * for sufficiently large input

* * {name}`Filter.atBot`
  * a preorder with no bottom
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
  * vacuously (every set is in `⊥`; see the gotcha in "Limit statements")

:::

The notations `𝓝`, `atTop`, `∀ᶠ` only parse after `open Filter Topology`.

{include 1 Phrasebook.Filters.Tendsto}

{include 1 Phrasebook.Filters.Proving}

{include 1 Phrasebook.Filters.EpsilonDelta}

{include 1 Phrasebook.Filters.Operations}
