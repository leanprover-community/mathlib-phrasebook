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

You have a limit statement in `Tendsto` or `∀ᶠ` form (see the
companion "Limit statements" entry for how to write one). This entry
covers the four recipes that close almost every proof: algebraic
combination, composition, `filter_upwards`, and `EventuallyEq`
substitution. For the ε-δ bridge, see "Bridges to ε-δ and filter
bases".

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
on the left. This matches function composition `g ∘ f`, not diagram
order.

# Strengthen an "eventually" fact: `filter_upwards`

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

# Limits depend only on eventual values: `EventuallyEq`

`f =ᶠ[l] g` ({name}`Filter.EventuallyEq`) means `f x = g x` holds
`l`-eventually. Anything that only depends on `l`-eventual behaviour
transfers from `f` to `g` for free; in particular,
`Tendsto f l m ↔ Tendsto g l m`.

The two lemmas you'll actually reach for:

* {name}`Filter.Tendsto.congr` — given `Tendsto f l m` and `f =ᶠ[l] g`,
  produces `Tendsto g l m`. Use as a one-step rewrite on a `Tendsto`
  you already have in hand.
* {name}`Filter.tendsto_congr'` — the same as an iff, when you want to
  rewrite both directions.

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

# Search hints

* Tendsto combinators: `Filter.Tendsto.*` (dot notation).
* Standard limits with no hypothesis: `tendsto_*`.
* Eventually facts: `Filter.Eventually.*`, `eventually_*`.
* Congruence by eventual equality: `Filter.Tendsto.congr`,
  `Filter.Tendsto.congr'`, `Filter.tendsto_congr'`.
