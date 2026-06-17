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

```lean -show
open Filter Topology
```

You have a limit statement in {name}`Tendsto` or `∀ᶠ` form (see the
companion {ref "filters-tendsto"}[Limit statements] entry for how to
write one). This entry covers five common recipes (algebraic
combination, composition, {tactic}`filter_upwards`, {name}`EventuallyEq`
substitution, and unfolding continuity to {name}`Tendsto`) that handle
most everyday goals. Other proofs lean on
monotonicity ({name}`Filter.Tendsto.mono_left`,
{name}`Filter.Eventually.mono`) or on {name}`map`/{name}`comap` (see
{ref "filters-operations"}[Operations on filters]). Stay in the
filter world; reach for {ref "filters-epsilon-delta"}[ε-δ] only when
translating from classical sources.

# Combine two convergent sequences

Algebraic operations on limits are all dot-style on {name}`Tendsto`:

::: leanSection
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

# Composition: {name}`Tendsto.comp`

::: leanSection
```lean -show
variable {α β γ : Type*}
variable {f : α → β} {g : β → γ}
variable {l₁ : Filter α} {l₂ : Filter β} {l₃ : Filter γ}
variable (hf : Tendsto f l₁ l₂) (hg : Tendsto g l₂ l₃)
```
```lean
example : Tendsto (g ∘ f) l₁ l₃ :=
  hg.comp hf
```

Note the order: {lean}`hg.comp hf`, with the *outer* function's {name}`Tendsto`
on the left. This matches function composition {lean}`g ∘ f`, not the
left-to-right `hf` then `hg` order you might expect.
:::

# Strengthen an "eventually" fact: {tactic}`filter_upwards`

When you have `∀ᶠ x in l, p₁ x` and `∀ᶠ x in l, p₂ x` and want
`∀ᶠ x in l, q x`, the tactic is {name}`Mathlib.Tactic.filterUpwards`:

```lean
example {u : ℕ → ℝ}
    (h1 : ∀ᶠ n in atTop, 0 ≤ u n)
    (h2 : ∀ᶠ n in atTop, u n ≤ 1) :
    ∀ᶠ n in atTop, u n ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [h1, h2] with n hn1 hn2
  exact ⟨hn1, hn2⟩
```

The `with n hn1 hn2` clause names the bound variable and the
strengthened hypotheses; you then prove the pointwise goal `q n`.
This is usually cleaner than combining {name}`Eventually.and` and {name}`Eventually.mono`
by hand.

# Limits depend only on eventual values: {name}`EventuallyEq`

:::leanSection
```lean -show
variable {α β : Type*} (f g : α → β) (l : Filter α) (m : Filter β) (x : α)
```
The {name}`Filter.EventuallyEq` relation, written {lean}`f =ᶠ[l] g`, means
{lean}`f x = g x` holds `l`-eventually. Anything that only depends on
`l`-eventual behaviour transfers from `f` to `g` for free; in
particular, {lean}`Tendsto f l m ↔ Tendsto g l m`.

The two lemmas you'll actually reach for:

* {name}`Filter.Tendsto.congr` takes {lean}`Tendsto f l m` and {lean}`f =ᶠ[l] g`
  and produces {lean}`Tendsto g l m`. Use as a one-step rewrite on a
  `Tendsto` you already have in hand.
* {name}`Filter.tendsto_congr'` is the same fact as an iff, when you
  want to rewrite both directions.
:::

```lean
example {f g : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a))
    (hfg : f =ᶠ[atTop] g) :
    Tendsto g atTop (𝓝 a) :=
  hf.congr' hfg
```

# Continuity at a point as a `Tendsto`

::: leanSection
```lean -show
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : X → Y) (x : X)
```
{lean}`ContinuousAt f x` *is* {lean}`Tendsto f (𝓝 x) (𝓝 (f x))`:

```lean
example (f : X → Y) (x : X) :
    ContinuousAt f x ↔ Tendsto f (𝓝 x) (𝓝 (f x)) :=
  Iff.rfl
```
:::

So every limit lemma is a continuity lemma, and vice versa. When proof
search for {name}`Continuous` stalls, unfolding through filters often
unblocks it.
