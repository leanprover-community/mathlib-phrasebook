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

The *reading* half of working with filters: how `≤`, `Filter.map`,
`Filter.comap`, and `Filter.prod` show up in Mathlib statements and
what they mean. You need this much algebra to read other people's
filter proofs and to recognise `Tendsto` in its native form.

# The order on filters

`F ≤ G` reads as "`F` is *finer* than `G`": every `G`-eventual set is
already `F`-eventual. Finer filter = more constraints, more like
"a single point".

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

* {name}`Filter.atTop_neBot`: requires `[Nonempty α] [SemilatticeSup α]`.
* `Filter.NeBot` on `𝓝 x`: automatic in any topological space.
* `Filter.map_neBot`: pushing a non-trivial filter forward stays
  non-trivial.

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
