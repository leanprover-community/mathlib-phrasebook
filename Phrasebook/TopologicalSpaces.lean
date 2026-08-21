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
that requires minimal background. In particular, we do not assume the reading is familiar with
filters. For an in depth tutorial of topology in Mathlib,
see the [topology chapter of Mathematics in
Lean](https://leanprover-community.github.io/mathematics_in_lean/C10_Topology.html).

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

Open-set lemmas are named `isOpen_...` or live in the {name}`IsOpen` namespace;
closed-set lemmas follow the same pattern. In particular, use {name}`IsOpen.inter` and
{name}`isOpen_iUnion` for finite intersections and arbitrary unions, and
{name}`IsClosed.union` and {name}`isClosed_iInter` for finite unions and arbitrary intersections.

The universal properties of interior and closure are often the shortest proof interface:
```lean
example (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) :=
  hs.inter ht

example (hst : s ⊆ t) (ht : IsClosed t) : closure s ⊆ t :=
  closure_minimal hst ht

example : x ∈ interior s ↔ s ∈ 𝓝 x :=
  mem_interior_iff_mem_nhds
```
The dual facts are {name}`interior_maximal` and {name}`subset_closure`; fixed-point forms are
{name}`IsOpen.interior_eq` and {name}`IsClosed.closure_eq`. For pointwise closure arguments,
{name}`mem_closure_iff` says that every open neighborhood meets the set. Density is usually
rewritten with {name}`dense_iff_closure_eq` or used through {name}`Dense.induction`.
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
in mathlib, such as {name}`LinearMap`.

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
These should generally only be used when you want to put some kind of structure on them.
For example, the vector space structure on {lean}`C(ℝ, ℝ)`

```lean
#synth Module ℝ C(ℝ, ℝ)
```

Some other function properties are {name}`IsOpenMap`, {name}`IsClosedMap`,
{name}`Topology.IsEmbedding`, {name}`Topology.IsOpenEmbedding`,
{name}`Topology.IsClosedEmbedding`, and {name}`Topology.IsQuotientMap`.
:::

# Building spaces

::: leanSection
```lean -show
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {s : Set X} {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
```

Mathlib supplies the usual topology automatically on subtypes, products, sums, dependent function
types, sigma types, and quotients. For example:
```lean
#synth TopologicalSpace s
#synth TopologicalSpace (X × Y)
#synth TopologicalSpace (∀ i, A i)
```
The subtype topology is induced by coercion, the product and function-space topologies make the
projections continuous, and quotient topologies are coinduced by the quotient map. Consequently,
the everyday constructors are {name}`continuous_subtype_val`, {name}`Continuous.subtype_mk`,
{name}`continuous_fst`, {name}`continuous_snd`, {name}`Continuous.prodMk`,
{name}`continuous_apply`, and {name}`continuous_pi`.

To build a topology explicitly, use:

* {name}`TopologicalSpace.induced` to pull a topology back along a map;
* {name}`TopologicalSpace.coinduced` to push one forward;
* {name}`TopologicalSpace.generateFrom` to generate one from a subbasis;
* {name}`TopologicalSpace.ofClosed` to specify the closed sets.

Their universal properties include {name}`continuous_iff_le_induced` and
{name}`continuous_iff_coinduced_le`.

Use {name}`TopologicalSpace.IsTopologicalBasis` to work with a basis; its most useful interfaces are
{name}`TopologicalSpace.IsTopologicalBasis.isOpen_iff`,
{name}`TopologicalSpace.IsTopologicalBasis.nhds_hasBasis`, and
{name}`TopologicalSpace.IsTopologicalBasis.continuous_iff`.

The order on topologies is reverse inclusion: `t₁ ≤ t₂` means that `t₁` is *finer* than `t₂`.
Thus `⊥` is the discrete topology and `⊤` is the indiscrete topology. When several topologies on
one type are in play, `open scoped Topology` enables `IsOpen[t]`, `IsClosed[t]`, `closure[t]`, and
`Continuous[t₁, t₂]`.
:::

# Properties of Topological Spaces

```lean -show
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
```

Some properties have both a form for sets as well as the whole space. For example,
{name}`IsCompact` is a predicate on {lean}`Set X` while {name}`CompactSpace` states that
{lean}`X` itself is compact. Note that {name}`CompactSpace` is a typeclass while {name}`IsCompact` is not.


Some other common properties that follow this are:

* connected: {name}`IsConnected` and {name}`ConnectedSpace`;
* path connected: {name}`IsPathConnected` and {name}`PathConnectedSpace`;

Unlike some textbook conventions, {name}`IsConnected` includes nonemptiness. Use
{name}`IsPreconnected` when the empty set should count.

Some common separation properties are:

* Hausdorff and locally compact: {name}`T2Space` and {name}`LocallyCompactSpace`;
* first/second countable: {name}`FirstCountableTopology` and {name}`SecondCountableTopology`;
* separable and discrete: {name}`TopologicalSpace.SeparableSpace` and {name}`DiscreteTopology`.

As an example of many of these properties, lets look at the proof that a coninuous function from
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
