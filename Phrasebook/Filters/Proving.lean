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

#doc (Manual) "Proving limits" =>
%%%
tag := "filters-proving"
%%%

You have a limit statement in `Tendsto` or `∀ᶠ` form (see the
companion {ref "filters-tendsto"}[Limit statements] entry for how to
write one). This entry covers four common recipes (algebraic
combination, composition, `filter_upwards`, and `EventuallyEq`
substitution) that handle most everyday goals. Other proofs lean on
monotonicity ({name}`Filter.Tendsto.mono_left`,
{name}`Filter.Eventually.mono`) or on `map`/`comap` (see
{ref "filters-operations"}[Operations on filters]). Stay in the
filter world; reach for ε-δ only when translating from classical
sources.

# Combine two convergent sequences

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

# Composition: `Tendsto.comp`

::: leanSection
```lean -show
open Filter Topology
variable {α β γ : Type*}
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
on the left. This matches function composition `g ∘ f`, not the
left-to-right `hf` then `hg` order you might expect.

# Strengthen an "eventually" fact: `filter_upwards`

When you have `∀ᶠ x in l, p₁ x` and `∀ᶠ x in l, p₂ x` and want
`∀ᶠ x in l, q x`, the tactic is {name}`Mathlib.Tactic.filterUpwards`:

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
strengthened hypotheses; you then prove the pointwise goal `q n`.
This is usually cleaner than combining `Eventually.and` and `.mono`
by hand.

# Limits depend only on eventual values: `EventuallyEq`

The {name}`Filter.EventuallyEq` relation, written `f =ᶠ[l] g`, means
`f x = g x` holds `l`-eventually. Anything that only depends on
`l`-eventual behaviour transfers from `f` to `g` for free; in
particular, `Tendsto f l m ↔ Tendsto g l m`.

The two lemmas you'll actually reach for:

* {name}`Filter.Tendsto.congr` takes `Tendsto f l m` and `f =ᶠ[l] g`
  and produces `Tendsto g l m`. Use as a one-step rewrite on a
  `Tendsto` you already have in hand.
* {name}`Filter.tendsto_congr'` is the same fact as an iff, when you
  want to rewrite both directions.

::: leanSection
```lean -show
open Filter Topology
```
```lean
example {f g : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a))
    (hfg : f =ᶠ[atTop] g) :
    Tendsto g atTop (𝓝 a) :=
  hf.congr' hfg
```
:::

# Continuity at a point as a `Tendsto`

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
