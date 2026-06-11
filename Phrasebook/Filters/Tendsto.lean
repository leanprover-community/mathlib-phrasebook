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

#doc (Manual) "Limit statements: `Tendsto` and `∀ᶠ`" =>
%%%
tag := "filters-tendsto"
%%%

This entry is about *writing* limits: how to turn a mathematical
statement (sequence convergence, "x → a", "almost everywhere", and so on)
into a Mathlib proposition. The companion
{ref "filters-proving"}[Proving limits] entry covers how to *prove* such a
statement once it is written.

# Write limits using `Tendsto`

Every limit statement goes through {name}`Filter.Tendsto`. That one
definition unifies the limits you would otherwise spell out separately:

::: leanSection
```lean -show
open Filter Topology
```
```lean
-- The sequence u : ℕ → ℝ converges to x as n → ∞
example (u : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto u atTop (𝓝 x)
-- The function f : ℝ → ℝ has limit L as x → a
example (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Tendsto f (𝓝 a) (𝓝 L)
-- The function f x tends to +∞ as x → +∞
example (f : ℝ → ℝ) : Prop :=
  Tendsto f atTop atTop
-- The function f has limit L as x → a from the right
example (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Tendsto f (𝓝[>] a) (𝓝 L)
```
:::

Under the hood, read `Tendsto f l₁ l₂` as "`f` sends `l₁` to `l₂`": every
set that is eventual for the target `l₂` has a preimage that is eventual
for the source `l₁`.

::: leanSection
```lean -show
open Filter Topology
variable {α β : Type*}
```
```lean
example (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Filter.tendsto_def
```
:::

# Punctured vs unpunctured limits
%%%
tag := "filters-punctured"
%%%

`Tendsto f (𝓝 a) (𝓝 L)` includes the behaviour of `f` *at* `a`, so
it forces `f a = L`. The *punctured* limit ("`x → a` with `x ≠ a`")
makes no claim about the value at `a` and lives on the punctured
neighbourhood filter `𝓝[≠] a`:

::: leanSection
```lean -show
open Filter Topology
```
```lean
example (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Tendsto f (𝓝[≠] a) (𝓝 L)
```
:::

So when you translate `lim_{x → a} f(x) = L` to Mathlib, ask
yourself whether the classical statement does or does not assume
continuity at `a`. If it does (the value at `a` is part of the
statement), use `𝓝 a`. If it doesn't (the punctured limit), use
`𝓝[≠] a`.

# Which filter goes where?

When you translate `lim_{x → x₀} f(x) = L` to `Tendsto f l₁ l₂`, the
recipe is mechanical:

1. *Source filter `l₁`*. What does the input `x` approach? "`n → ∞`" is
   `atTop`. "`x → a` from the right" is `𝓝[>] a`. "`x → a` in `s`" is
   `𝓝[s] a`. "for almost every `ω`" is `μ.ae`.
2. *Target filter `l₂`*. What does `f(x)` approach? "→ L" is `𝓝 L`. "→
   +∞" is `atTop`. "→ value in `t`" is `𝓟 t` (the principal filter on
   `t`).

If you keep this in mind, almost every classical limit translates by
inspection.

# `∀ᶠ` and `∃ᶠ`: eventually and frequently

The {name}`Filter.Eventually` relation, written `∀ᶠ x in l, p x`,
means "the set where `p` holds belongs to `l`". The dual
{name}`Filter.Frequently`, written `∃ᶠ x in l, p x`, means "the set
where `p` fails does *not* belong to `l`" (equivalently, `p` is not
eventually false).

For the standard filters:

::: table +header

* * Form
  * Reads as

* * `∀ᶠ x in 𝓝 a, p x`
  * `p` holds on a neighbourhood of `a`

* * `∀ᶠ n in atTop, p n`
  * `p` holds for all sufficiently large `n`

* * `∀ᵐ x ∂μ, p x`
  * `p` holds almost everywhere (sugar for `∀ᶠ x in μ.ae, p x`)

* * `∃ᶠ n in atTop, p n`
  * `p` holds infinitely often

:::

# Gotchas

*`Tendsto` direction.* Source filter first, target filter second. The
mnemonic "`f` sends `l₁` to `l₂`" matches the type
`Filter α → Filter β` (composition direction), not the limit
arrow `lim x → a`. The trivial filter `⊥` contains every set, so
`Tendsto f ⊥ l` is _vacuously true_ for any `l`. Accidentally writing
a degenerate source (e.g. `𝓝[s] a` for an `a` outside the closure of
`s`) leaves you with hypotheses that prove nothing.

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
