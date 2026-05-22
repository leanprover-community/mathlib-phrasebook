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

#doc (Manual) "Filters" =>

A *filter* on `α` is Mathlib's universal device for talking about
"limiting behaviour". A single definition — {name}`Filter` — encodes
neighbourhoods of a point, "x → ∞", almost-everywhere statements,
convergence along a subsequence, and "all but finitely many points";
a single relation — {name}`Filter.Tendsto` — covers every limit you
would otherwise have to redefine. Internalising this collapses a lot
of analysis API into something you can predict.

To declare a filter:

::: leanSection
```lean
variable {α : Type*} (l : Filter α)
```
:::

The intuition: an element of `l` is a "large" subset of `α`. Filters are
upward closed and closed under finite intersections, so "large" behaves
like you expect — supersets and finite intersections of large sets are
large.

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
  * always (every set is large)

* * `⊥`
  * any
  * vacuously (no set is large enough — see gotchas)

:::

The notations `𝓝`, `atTop`, `∀ᶠ` only parse after `open Filter Topology`.

# `Tendsto`: the universal limit

Every limit statement goes through {name}`Filter.Tendsto`:

::: leanSection
```lean -show
open Filter Topology
variable {β : Type*}
```
```lean
example (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Filter.tendsto_def
```
:::

Read it as "`f` sends `l₁` to `l₂`": preimages of large sets in the
codomain stay large in the domain. That one definition unifies the
limits you would otherwise spell out separately:

::: leanSection
```lean -show
open Filter Topology
```
```lean
-- u : ℕ → ℝ converges to x
example (u : ℕ → ℝ) (x : ℝ) :
    Prop := Tendsto u atTop (𝓝 x)
-- f : ℝ → ℝ has limit L at a
example (f : ℝ → ℝ) (a L : ℝ) :
    Prop := Tendsto f (𝓝 a) (𝓝 L)
-- f tends to +∞ as x → +∞
example (f : ℝ → ℝ) :
    Prop := Tendsto f atTop atTop
-- one-sided limit
example (f : ℝ → ℝ) (a L : ℝ) :
    Prop := Tendsto f (𝓝[>] a) (𝓝 L)
```
:::

# Which filter goes where?

When you translate `lim x → α, f x = β` to `Tendsto f l₁ l₂`, the
recipe is mechanical:

1. *Source filter `l₁`*. What does the input `x` approach? "`n → ∞`" is
   `atTop`. "`x → a` from the right" is `𝓝[>] a`. "`x → a` in `s`" is
   `𝓝[s] a`. "for almost every `ω`" is `μ.ae`.
2. *Target filter `l₂`*. What does `f(x)` approach? "→ L" is `𝓝 L`. "→
   +∞" is `atTop`. "→ value in `t`" is `𝓟 t` (the principal filter on
   `t`).

If you keep this in mind, almost every classical limit translates by
inspection. The codomain-then-domain confusion is more common than the
underlying mathematics: it's why the gotcha below exists.

# `∀ᶠ` and `∃ᶠ`: eventually and frequently

`∀ᶠ x in l, p x` ({name}`Filter.Eventually`) means "the set where `p`
holds belongs to `l`". `∃ᶠ x in l, p x` ({name}`Filter.Frequently`) is
its dual.

For the filters above:

::: table +header

* * Form
  * Reads as

* * `∀ᶠ x in 𝓝 a, p x`
  * `p` holds on a neighbourhood of `a`

* * `∀ᶠ n in atTop, p n`
  * `p` holds for all sufficiently large `n`

* * `∀ᵐ x ∂μ, p x` (= `∀ᶠ x in μ.ae, p x`)
  * `p` holds almost everywhere

* * `∃ᶠ n in atTop, p n`
  * `p` holds infinitely often

:::

The tactic `filter_upwards [h₁, h₂] with x hx₁ hx₂` is the bread and
butter: it discharges a goal `∀ᶠ x in l, q x` from `∀ᶠ x in l, p₁ x`
and `∀ᶠ x in l, p₂ x`, opening a pointwise goal where `hx₁ : p₁ x` and
`hx₂ : p₂ x`.

# Patterns and recipes

## Recipe: combine two convergent sequences

Algebraic operations on limits are all dot-style on `Tendsto`:

::: leanSection
```lean -show
open Filter Topology
```
```lean
example {u v : ℕ → ℝ} {a b : ℝ}
    (hu : Tendsto u atTop (𝓝 a))
    (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n => u n + v n) atTop (𝓝 (a + b)) :=
  hu.add hv

example {u : ℕ → ℝ} {a c : ℝ}
    (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => c * u n) atTop (𝓝 (c * a)) :=
  tendsto_const_nhds.mul hu
```
:::

The general pattern: `Tendsto.<op>` for every algebraic operation that
makes sense. {name}`Filter.Tendsto.add`,
{name}`Filter.Tendsto.mul`, {name}`Filter.Tendsto.const_smul`,
{name}`Filter.Tendsto.neg`. Constants come from
{name}`tendsto_const_nhds`.

## Recipe: change of variables (`Tendsto.comp`)

::: leanSection
```lean -show
open Filter Topology
variable {β γ : Type*}
```
```lean
example {f : α → β} {g : β → γ}
    {l₁ : Filter α} {l₂ : Filter β} {l₃ : Filter γ}
    (hf : Tendsto f l₁ l₂) (hg : Tendsto g l₂ l₃) :
    Tendsto (g ∘ f) l₁ l₃ :=
  hg.comp hf
```
:::

Note the order: `(hg.comp hf)`, with the *outer* function's `Tendsto`
on the left. This matches function composition `g ∘ f`, not diagram
order.

## Recipe: limits depend only on eventual values

`f =ᶠ[l] g` ({name}`Filter.EventuallyEq`) means the set
`{x | f x = g x}` is large in `l`. Anything that only depends on
`l`-eventual behaviour transfers from `f` to `g` for free; in
particular, `Tendsto f l m ↔ Tendsto g l m`.

The two lemmas you'll actually reach for:

* {name}`Filter.Tendsto.congr` — given `Tendsto f l m` and `f =ᶠ[l] g`,
  produces `Tendsto g l m`. Use as a one-step rewrite on a `Tendsto`
  you already have in hand.
* {name}`Filter.tendsto_congr'` — the same as an iff, when you want to
  rewrite both directions.

::: leanSection
```lean -show
open Filter Topology
variable {α : Type*}
```
```lean
example {f g : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a))
    (hfg : f =ᶠ[atTop] g) :
    Tendsto g atTop (𝓝 a) :=
  hf.congr' hfg
```
:::

The order-relation analogue is `f ≤ᶠ[l] g` ({name}`Filter.EventuallyLE`),
used in squeeze theorems and liminf/limsup arguments.

## Recipe: joint limits with `Filter.prod` (`×ˢ`)

`F ×ˢ G : Filter (α × β)` is the product filter: its large sets are
those containing a rectangle `s ×ˢ t` with `s ∈ F` and `t ∈ G`. The
notation `×ˢ` covers both `Set.prod` and `Filter.prod`; the elaborator
disambiguates from the types.

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
operations (`+`, `*`, `•`). To go the other way — package two
continuous functions *into* a product — reach for
{name}`Continuous.prodMk`.

## Recipe: strengthening an "eventually" fact

When you have `∀ᶠ x in l, p₁ x` and `∀ᶠ x in l, p₂ x` and want
`∀ᶠ x in l, q x`, the tactic is `filter_upwards`:

::: leanSection
```lean -show
open Filter Topology
```
```lean
example {u : ℕ → ℝ}
    (h1 : ∀ᶠ n in atTop, 0 ≤ u n)
    (h2 : ∀ᶠ n in atTop, u n ≤ 1) :
    ∀ᶠ n in atTop, u n ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [h1, h2] with n hn1 hn2
  exact ⟨hn1, hn2⟩
```
:::

The `with n hn1 hn2` clause names the bound variable and the
strengthened hypotheses; you then prove the pointwise goal `q n`. This
is the tactic to reach for *every time* you'd otherwise want to use
`Eventually.and` plus a `.mono`.

## Recipe: turn a `Tendsto` into ε-δ (and back)

Mathlib statements are usually in `Tendsto` form, but your hands often
have ε-δ data. The bridges are filter-basis lemmas:

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

The same trick applies to `atTop` (use {name}`Metric.tendsto_nhds` and
variants), to {name}`Filter.HasBasis.tendsto_iff` for arbitrary filter
bases, and to `Metric.tendsto_atTop` for sequence limits.

## Recipe: continuity at a point as a `Tendsto`

`ContinuousAt f x` *is* `Tendsto f (𝓝 x) (𝓝 (f x))`:

::: leanSection
```lean -show
open Filter Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
```
```lean
example (f : X → Y) (x : X) :
    ContinuousAt f x ↔ Tendsto f (𝓝 x) (𝓝 (f x)) :=
  Iff.rfl
```
:::

So every limit lemma is a continuity lemma, and vice versa. When proof
search for `Continuous` stalls, unfolding through filters often
unblocks it.

# Reading Mathlib proofs

The five idiomatic shapes you'll encounter:

1. *Algebraic combination of limits.*
   ```
   hu.add hv      -- f + g converges to a + b
   hu.mul hv      -- f * g converges
   hu.const_smul  -- c • f converges
   ```

2. *Composition.* `hg.comp hf` for `Tendsto (g ∘ f) l₁ l₃`.

3. *`filter_upwards [h₁, h₂] with x hx₁ hx₂`* for `∀ᶠ`-goals built from
   `∀ᶠ`-hypotheses. The pointwise reasoning lives after `with`.

4. *Transporting an eventual property along a limit.*
   `hf.eventually hp` turns `∀ᶠ y in l₂, p y` and `Tendsto f l₁ l₂`
   into `∀ᶠ x in l₁, p (f x)` ({name}`Filter.Tendsto.eventually`).

5. *Going through a basis.* `(hl.tendsto_iff hl').mpr h` when you have
   bases for both filters and want to assemble a `Tendsto` from
   pointwise data.

# The order on filters

`F ≤ G` reads as "`F` is *finer* than `G`": every large set of `G` is
already large for `F`. Finer filter = more constraints, more like
"a single point".

The mnemonic that prevents the sign-flip everyone trips over: on
principal filters, the order is just inclusion of the underlying
sets —

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
  * every set is large (vacuous; see gotchas)

* * `⊤`
  * only `Set.univ` is large

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

Buzzard's pearl, useful at 2am: a filter is determined by what
contains it, not by what it contains.

# Push-forward and pull-back

For `f : α → β`:

* {name}`Filter.map` `f F : Filter β` — push-forward. A set `t` is
  large iff its preimage `f ⁻¹' t` is large in `F`.
* {name}`Filter.comap` `f G : Filter α` — pull-back. A set `s` is
  large iff it contains the preimage of some `G`-large set.

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

`map` and `comap` form a Galois connection:

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
author is choosing to manipulate filters algebraically — no pointwise
reasoning. A common shape: a `Tendsto u (atTop.comap φ) _` boils down
a "limit along the subsequence `φ`" to one along `atTop`.

# Gotchas

*`Tendsto` direction.* Source filter first, target filter second. The
mnemonic "`f` sends `l₁` to `l₂`" matches the type
`Filter α → Filter β` (composition direction), not the limit
arrow `lim x → a`.

*`⊥` is not "doesn't converge".* The trivial filter `⊥` contains every
set, so `Tendsto f ⊥ l` is _vacuously true_ for any `l`. If you write
this by accident — e.g. by `Tendsto f (𝓝[s] a) _` where `s` doesn't
accumulate at `a` — your hypotheses give you nothing useful.

*`NeBot`: when a filter isn't trivial.* `[Filter.NeBot l]` is the
typeclass asserting `l ≠ ⊥`. Many limit lemmas — anything that pulls
a witness out of a `∀ᶠ`, in particular — require it, because over `⊥`
everything is vacuously true. Common instances fire automatically:

* {name}`Filter.atTop_neBot` — under `[Nonempty α] [SemilatticeSup α]`.
* `Filter.NeBot` on `𝓝 x` — automatic in any topological space.
* `Filter.map_neBot` — pushing a non-trivial filter forward stays
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
fire and the proof goes through. A degenerate `𝓝[s] a` is the most
common *live* source of "missing `NeBot`" — the cross-reference is
`mem_closure_iff_nhdsWithin_neBot` (in the next gotcha).

*`𝓝` vs `𝓝[s]` at boundary points.* `𝓝[s] a` is the neighbourhood
filter of `a` restricted to `s`; at a point `a` not in the closure of
`s`, it degenerates to `⊥` (see above). The relevant lemma is
`mem_closure_iff_nhdsWithin_neBot`.

*Punctured vs unpunctured.* `Tendsto f (𝓝 a) (𝓝 L)` includes
behaviour *at* `a` — if `f a ≠ L`, you cannot have this. For the
classical "limit as `x → a` with `x ≠ a`", use `𝓝[≠] a`.

*`open` matters.* `𝓝`, `𝓝[s]`, `𝓝[>]`, `𝓝[<]`, `atTop`, `atBot`,
`∀ᶠ`, `∃ᶠ` all need `open Filter Topology` to parse. Concretely, in
a fresh section where `Topology` isn't open:

::: leanSection
```lean +error (name := nhdsNotOpened)
example : Filter ℝ := 𝓝 (0 : ℝ)
```
```leanOutput nhdsNotOpened
Unknown identifier `𝓝`
```
:::

After `open Topology` (and `open Filter` for `∀ᶠ`, `atTop`, etc.) the
same line elaborates without complaint.

# Filter bases

To work with a concrete description of a filter, use
{name}`Filter.HasBasis`: a filter `l` has basis `p, s` iff its members
are exactly the supersets of `s i` for some `i` with `p i`. The
membership lemma is {name}`Filter.HasBasis.mem_iff`, and
{name}`Filter.HasBasis.tendsto_iff` turns `Tendsto` into an ε-δ-style
statement.

Common bases:

* {name}`Metric.nhds_basis_ball` — neighbourhoods of `x` have basis the
  open balls around `x`.
* {name}`Filter.atTop_basis` — `atTop` has basis the sets `Ici n`.

Pattern: when you need to *use* a filter (extract a witness from
membership), apply `HasBasis.mem_iff` to drop into the parametrised
sets. When you need to *prove* a filter property, apply
`HasBasis.tendsto_iff` or {name}`Filter.HasBasis.eventually_iff`.

# Search hints

* Tendsto combinators: `Filter.Tendsto.*` (dot notation).
* Standard limits with no hypothesis: `tendsto_*`.
* Eventually facts: `Filter.Eventually.*`, `eventually_*`.
* Filter bases: `Filter.HasBasis.*`.
* The bridge between filters and ε-δ on a metric space:
  `Metric.tendsto_*`.

# See also

* [Limits](Phrasebook/Limits.lean) — the everyday forms of `Tendsto`.
* [Topology](Phrasebook/Topology.lean) — `ContinuousAt` in terms of `𝓝`.
* [Metric spaces](Phrasebook/MetricSpaces.lean) — ε-δ via filter bases.
* [Measure theory](Phrasebook/MeasureTheory.lean) — `μ.ae` and almost
  everywhere.
