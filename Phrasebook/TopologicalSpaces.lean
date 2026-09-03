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

#doc (Manual) "Topological spaces" =>
%%%
tag := "topological-spaces"
%%%

The goal of this chapter is to give an introduction to the language of topology in Mathlib
that requires minimal background. In particular, we do not assume the reader is familiar with
filters. For an in depth tutorial of topology in Mathlib,
see the topology chapter of [Mathematics in
Lean](https://leanprover-community.github.io/mathematics_in_lean/C11_Topology.html).

For an introduction to filters and how they are used to describe limits and convergence; see
{ref "filters-tendsto"}[Limit statements] and {ref "filters-proving"}[Proving limits].

# Basic language

To say "Let `X` be a topological space", we write

:::: leanSection
```lean
variable (X : Type*) [TopologicalSpace X]
```
```lean -show
open Set Filter Topology
variable {Y : Type*} [TopologicalSpace Y]
variable {s t : Set X} {x : X} {f : X → Y}
```

This comes with a predicate {name}`IsOpen` on {lean}`Set X` telling us which subsets of `X` are open.

```lean
#check IsOpen
```

So to state that the union of two open subsets is open, we would write
```lean
example (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) :=
  IsOpen.union hs ht
```

Some other common properties of subsets are:

::: table +header

* * Mathematics
  * Mathlib

* * `s` is closed / clopen
  * {lean}`IsClosed s` / {lean}`IsClopen s`

* * interior / closure of `s`
  * {lean}`interior s` / {lean}`closure s`

* * `s` is dense
  * {lean}`Dense s`

:::
::::

# Continuous maps

::: leanSection
```lean -show
open Set Topology
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {s : Set X} {x : X} {f : X → Y} {g : Y → Z}
```

If {lean}`f` is a function from {lean}`X` to {lean}`Y`, then to say "`f` is continuous", we write

```lean
#check Continuous f
```

Note that {name}`Continuous` is unbundled, as opposed to how many types of functions are implemented
in Mathlib, such as {name}`LinearMap`.

```lean
example (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) :=
  hg.comp hf
```

For routine continuity goals, try `fun_prop`:
```lean
example : Continuous (fun p : X × Y => (p.2, p.1)) := by
  fun_prop

example : Continuous (fun x : ℝ => x^2 + 1) := by
  fun_prop
```

To state that a function is a homeomorphism, use {name}`IsHomeomorph`.

```lean
#check IsHomeomorph
```

The bundled versions of continous maps and homeomorphisms are {name}`ContinuousMap` (which can be
written using the notation {lean}`C(X, Y)`) and {name}`Homeomorph` (which can be written as {lean}`X ≃ₜ Y`).
These are useful when you want to put some structure on the collection of all continuous maps.
For example, the vector space structure on {lean}`C(ℝ, ℝ)`.

```lean
#synth Module ℝ C(ℝ, ℝ)
```

```lean -show
variable (hf : Continuous f)
```

The proof that a {name}`ContinuousMap` is continuous is {name}`map_continuous`. Given
a function {lean}`f` and a proof it is continuous {lean}`(hf : Continuous f)`, you can construct the corresponding
{lean}`ContinuousMap` as {lean}`ContinuousMap.mk f hf` or simply `⟨f, hf⟩`.

```lean
#check (⟨f, hf⟩ : C(X, Y))
```

```lean -show
variable (hf : IsHomeomorph f)
```

```lean -show
variable (hf : IsHomeomorph f)
```

{name}`Homeomorph` is a bit different as it bundles together both the function and its inverse, so
there is more data contained here than just a function and a proof of {name}`IsHomeomorph`.
To upgrade an {name}`Equiv` to a {name}`Homeomorph`, use
{name}`Equiv.toHomeomorph`. This is the prefered way of constructing homeomorphisms.
Given a proof of {lean}`(hf : IsHomeomorph f)`, you can construct the corresponding {name}`Homeomorph`
as {lean}`hf.homeomorph` but this should only be done when you don't have a constructive way of
defining the inverse of {lean}`f`. To go from a {name}`Homeomorph` to a {name}`ContinuousMap`, use
{name}`map_continuous`.

Some other function properties are {name}`IsOpenMap`, {name}`IsClosedMap`,
{name}`Topology.IsEmbedding`, {name}`Topology.IsOpenEmbedding`,
{name}`Topology.IsClosedEmbedding`, and {name}`Topology.IsQuotientMap`.
:::

# Properties of Topological Spaces

```lean -show
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
```

Some properties have both a form for sets as well as the whole space. For example,
{name}`IsCompact` is a predicate on {lean}`Set X` while {name}`CompactSpace` states that
{lean}`X` itself is compact. Note that {name}`CompactSpace` is a typeclass while {name}`IsCompact` is not.


Some other common properties that follow this are:

* {name}`IsConnected` and {name}`ConnectedSpace`;
* {name}`IsPathConnected` and {name}`PathConnectedSpace`;

Unlike some textbook conventions, {name}`IsConnected` includes nonemptiness. Use
{name}`IsPreconnected` when the empty set should count.

Some common separation properties are:

* Hausdorff and locally compact: {name}`T2Space` and {name}`LocallyCompactSpace`;
* first/second countable: {name}`FirstCountableTopology` and {name}`SecondCountableTopology`;
* separable and discrete: {name}`TopologicalSpace.SeparableSpace` and {name}`DiscreteTopology`.

As an example using some of these properties, lets look at the proof that a continuous function from
a compact space to a Hausdorff space is closed.

```lean
example {f : X → Y} (hf : Continuous f)
    [CompactSpace X] [T2Space Y] :
    IsClosedMap f := by
  intro s hs
  have : IsCompact s := hs.isCompact
  have : IsCompact (f '' s) := this.image hf
  exact this.isClosed
```
