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

#doc (Manual) "Operations on filters" =>
%%%
tag := "filters-operations"
%%%

Sometimes you need to read filter algebra rather than write a limit: a
proof you are following pivots through `≤`, `Filter.map`, `Filter.comap`,
or `Filter.prod`, or you want to reshape a `Tendsto` goal into an
equivalent one. This entry explains what those operations mean and the
goal each one serves.

# The order on filters

`F ≤ G` reads as "`F` is *finer* than `G`": every `G`-eventual set is
already `F`-eventual. A finer filter carries more constraints and sits
closer to "a single point".

This order is what lets you weaken a limit. Say you have
`Tendsto f G (𝓝 L)` and want `Tendsto f F (𝓝 L)` for a finer source
`F ≤ G`. Then {name}`Filter.Tendsto.mono_left` reduces the goal to proving
`F ≤ G`: convergence along a coarser filter implies convergence along any
finer one. For instance a two-sided limit gives the one-sided limit,
because `𝓝[>] a ≤ 𝓝 a`.

The mnemonic that prevents the sign-flip everyone trips over: on
principal filters, the order is just inclusion of the underlying
sets:

::: leanSection
```lean -show
open Filter Topology
variable {α : Type*}
```
```lean
example (s t : Set α) :
    𝓟 s ≤ 𝓟 t ↔ s ⊆ t :=
  Filter.principal_mono
```
:::

The lattice on `Filter α`:

::: table +header

* * Filter
  * "Eventually in this filter" means

* * `F ⊓ G`
  * eventually for both `F` and `G`

* * `F ⊔ G`
  * eventually for either `F` or `G`

* * `⊥`
  * every set is `⊥`-eventual (vacuous; see `NeBot` below)

* * `⊤`
  * only `Set.univ` is `⊤`-eventual ("everywhere")

:::

This is exactly why `nhdsWithin x s = 𝓝 x ⊓ 𝓟 s`: "near `x` *and* in
`s`":

::: leanSection
```lean -show
open Filter Topology
variable {X : Type*} [TopologicalSpace X]
```
```lean
example (x : X) (s : Set X) :
    𝓝[s] x = 𝓝 x ⊓ 𝓟 s :=
  rfl
```
:::

# Push-forward and pull-back: `Filter.map` and `Filter.comap`

For `f : α → β`:

* {name}`Filter.map` `f F : Filter β` is the *push-forward*. A set
  `t` is `map f F`-eventual iff its preimage `f ⁻¹' t` is `F`-eventual.
* {name}`Filter.comap` `f G : Filter α` is the *pull-back*. A set `s`
  is `comap f G`-eventual iff it contains the preimage of some
  `G`-eventual set.

These are the algebraic content of `Tendsto`. By definition:

::: leanSection
```lean -show
open Filter Topology
variable {α β : Type*}
```
```lean
example (f : α → β) (F : Filter α) (G : Filter β) :
    Tendsto f F G ↔ Filter.map f F ≤ G :=
  Iff.rfl
```
:::

`map` and `comap` form a {name}`GaloisConnection`:

::: leanSection
```lean -show
open Filter Topology
variable {α β : Type*}
```
```lean
example (f : α → β) (F : Filter α) (G : Filter β) :
    Filter.map f F ≤ G ↔ F ≤ Filter.comap f G :=
  Filter.map_le_iff_le_comap
```
:::

When you read a proof that pivots through `.map` or `.comap`, the
author is manipulating filters algebraically. A common shape is
`Tendsto u (atTop.comap φ) _`, which expresses "a limit along the
subsequence `φ`" as a `Tendsto` along `atTop`.

# Joint limits with `Filter.prod` (`×ˢ`)

`F ×ˢ G : Filter (α × β)` is the product filter: a set is
`F ×ˢ G`-eventual iff it contains a rectangle `s ×ˢ t` with `s ∈ F`
and `t ∈ G`. The notation `×ˢ` covers both `Set.prod` and
`Filter.prod`; the elaborator disambiguates from the types.

The single fact that drives every joint-limit proof:

::: leanSection
```lean -show
open Filter Topology
variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
```
```lean
example (x : α) (y : β) :
    𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y :=
  nhds_prod_eq
```
:::

So a two-variable continuity statement is just a `Tendsto` on a
product filter:

::: leanSection
```lean -show
open Filter Topology
```
```lean
example (x y : ℝ) :
    Tendsto (fun p : ℝ × ℝ => p.1 + p.2)
      (𝓝 (x, y)) (𝓝 (x + y)) := by
  rw [nhds_prod_eq]
  -- New goal: Tendsto _ (𝓝 x ×ˢ 𝓝 y) (𝓝 (x + y))
  exact tendsto_fst.add tendsto_snd
```
:::

This is exactly how Mathlib phrases continuity of two-variable
operations (`+`, `*`, `•`). To go the other way (package two
continuous functions *into* a product), reach for
{name}`Continuous.prodMk`.

# `NeBot`: when a filter isn't trivial

`[Filter.NeBot l]` is the typeclass asserting `l ≠ ⊥`. Many limit
lemmas (anything that pulls a witness out of a `∀ᶠ`, in particular)
require it, because over `⊥` everything is vacuously true. Common
instances fire automatically:

* `atTop` on a nonempty `[SemilatticeSup α]` (the instance is
  {name}`Filter.atTop_neBot`).
* `𝓝 x` in any topological space.
* `Filter.map f F` whenever `F` is non-trivial.

The instance for `atTop` requires `[Nonempty α]`; forget it and
typeclass synthesis fails:

::: leanSection
```lean +error (name := neBotMissing)
open Filter in
example {α : Type*} [SemilatticeSup α] (s : Set α)
    (hs : ∀ᶠ x in (atTop : Filter α), x ∈ s) : s.Nonempty :=
  hs.exists
```
```leanOutput neBotMissing
failed to synthesize instance of type class
  atTop.NeBot

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
:::

Adding `[Nonempty α]` to the variables makes {name}`Filter.atTop_neBot`
fire and the proof goes through.

# Reference: the standard filters
%%%
tag := "filters-table"
%%%

Every limit in this chapter is a `Tendsto` (or `∀ᶠ`) between two of the
filters below. To translate a classical statement, read off the source
and target from this table.

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

* * `ae μ`
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
  * vacuously (every set is in `⊥`; see the
    {ref "filters-tendsto"}[Limit statements] gotcha)

:::
