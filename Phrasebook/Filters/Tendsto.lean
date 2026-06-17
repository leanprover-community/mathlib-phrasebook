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

Before anything parses you need `open Filter Topology` in scope: the
notations `𝓝`, `𝓝[s]`, `𝓝[>]`, `𝓝[<]`, `atTop`, `atBot`, `∀ᶠ`, `∃ᶠ` are
all defined there. Without it you get an "unknown identifier":

::: leanSection
```lean +error (name := nhdsNotOpened)
example : Filter ℝ := 𝓝 (0 : ℝ)
```
```leanOutput nhdsNotOpened
Unknown identifier `𝓝`
```
:::

Every example below assumes the `open` has happened.
```lean -show
open Filter Topology
```

# Write limits using `Tendsto`

Every limit statement goes through {name}`Filter.Tendsto`. That one
definition unifies the limits you would otherwise spell out separately:

::: leanSection
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

These four are not the only forms; any source-and-target pair of filters
is a limit statement. The {ref "filters-table"}[reference table at the end
of the chapter] lists the standard filters you can drop into either slot.

Under the hood, read `Tendsto f l₁ l₂` as "`f` sends `l₁` to `l₂`": every
set that is eventual for the target `l₂` has a preimage that is eventual
for the source `l₁`.

::: leanSection
```lean
example (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Filter.tendsto_def
```
:::

# Which filter goes where?

When you translate `lim_{x → x₀} f(x) = L` to `Tendsto f l₁ l₂`, the
recipe is mechanical:

1. *Source filter `l₁`*. What does the input `x` approach? "`n → ∞`" is
   `atTop`. "`x → a` from the right" is `𝓝[>] a`. "`x → a` in `s`" is
   `𝓝[s] a`. "for almost every `ω`" is `ae μ`.
2. *Target filter `l₂`*. What does `f(x)` approach? "→ L" is `𝓝 L`. "→
   +∞" is `atTop`. "→ value in `t`" is `𝓟 t` (the principal filter on
   `t`).

If you keep this in mind, almost every classical limit translates by
inspection.

# Punctured vs unpunctured limits
%%%
tag := "filters-punctured"
%%%

::: leanSection
```lean -show
variable (f : ℝ → ℝ) (a L : ℝ)
```
There is one choice the mechanical recipe leaves open. {lean}`Tendsto f (𝓝 a) (𝓝 L)`
includes the behaviour of `f` *at* `a`, so it forces `f a = L`. The
*punctured* limit ("`x → a` with `x ≠ a`") makes no claim about the value
at `a` and lives on the punctured neighbourhood filter `𝓝[≠] a`:

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

# `∀ᶠ` and `∃ᶠ`: eventually and frequently

`∀ᶠ x in l, p x` says `p` holds *eventually* along `l`: on a neighbourhood
of the point, for all sufficiently large `n`, almost everywhere — whichever
notion `l` carries. `∃ᶠ x in l, p x` is the dual, "`p` holds *frequently*":
infinitely often, or on arbitrarily large inputs. Concretely, `∀ᶠ x in l,
p x` means the set where `p` holds lies in `l`, and `∃ᶠ x in l, p x` means
the set where `p` fails does not (equivalently, `p` is not eventually
false); the underlying relations are {name}`Filter.Eventually` and
{name}`Filter.Frequently`.

For the standard filters:

::: table +header

* * Form
  * Reads as

* * `∀ᶠ x in 𝓝 a, p x`
  * `p` holds on a neighbourhood of `a`

* * `∀ᶠ n in atTop, p n`
  * `p` holds for all sufficiently large `n`

* * `∀ᵐ x ∂μ, p x`
  * `p` holds almost everywhere (sugar for `∀ᶠ x in ae μ, p x`)

* * `∃ᶠ n in atTop, p n`
  * `p` holds infinitely often

:::

# Gotchas

:::leanSection
```lean -show
variable (f : ℝ → ℝ) (l l₁ l₂ : Filter ℝ) (u : ℕ → ℝ) (x : ℝ)
```
*Source first, target second.* {lean}`Tendsto f l₁ l₂` takes the source filter
`l₁` before the target `l₂`, the opposite order from the arrow in
`lim_{x → a} f(x) = L`, where you name the target `L` last. When in doubt,
recall the meaning "`f` sends `l₁` to `l₂`" and push the source forward to
the target: a sequence limit is {lean}`Tendsto u atTop (𝓝 x)`, with {name}`atTop`
(where `n` lives) first.

*The trivial filter proves nothing.* `⊥` contains every set, so
{lean}`Tendsto f ⊥ l` is _vacuously true_ for any `l`. A degenerate source
(for instance `𝓝[s] a` for an `a` outside the closure of `s`, which equals
`⊥`) leaves you with hypotheses that prove nothing.
:::
