/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
-- Write a code block with ```savedLean ... ``` to save it to an external file.
open Verso.Genre.Manual.InlineLean


open Phrasebook

set_option pp.rawOnError true

#doc (Manual) "Asymptotics" =>

We outline some features of Mathlib's support for Landau notation.

Much the API for Landau notation belongs to the following two namespaces which we open here:
```lean
open Asymptotics Filter
```

# First examples
Given two sequences of real numbers, $`a_n` and $`b_n`, Mathlib allows one to say that $`a = O(b)`
by writing simply `a =O[atTop] b`. We can witness that this means what we expect as follows:
```lean
example (a b : ℕ → ℝ) :
    a =O[atTop] b ↔
      ∃ C N, ∀ n ≥ N, ‖a n‖ ≤ C * ‖b n‖ := by
  simp_rw [isBigO_iff, eventually_atTop]
```
If instead we have functions $`f, g : ℝ → ℝ`, the same notation works:
```lean
example (f g : ℝ → ℝ) :
    f =O[atTop] g ↔
      ∃ C N, ∀ n ≥ N, ‖f n‖ ≤ C * ‖g n‖ := by
  simp_rw [isBigO_iff, eventually_atTop]
```

# General case and further notation

The definition underlying the notation introduced above is {name}`IsBigO`. This definition applies
to functions whose domain carries a filter and whose codomains carry a norm. For simplicity here
we will assume the functions take values in the same codomain and this this is actually a normed
group.
```lean
variable {α E : Type*}
  (l : Filter α) [NormedAddCommGroup E]
  (f g : α → E)
```
In this setting, we can witness Mathlib's support for further Landau notation as follows:
- {lean}`f =O[l] g` notation for {name}`IsBigO`
- {lean}`f =Θ[l] g` notation for {name}`IsTheta`
- {lean}`f =o[l] g` notation for {name}`IsLittleO`
- {lean}`f ~[l] g` notation for {name}`IsEquivalent`

We note some familiar properties:
```lean
example : f =Θ[l] g ↔ f =O[l] g ∧ g =O[l] f := Iff.rfl

example : f ~[l] g ↔ (f - g) =o[l] g := Iff.rfl
```

We also note that there exists a more quantiative variant of {name}`IsBigO` which
allows control over the constant, this is {name}`IsBigOWith`.

# Unnormed topological vector spaces

Mathlib also provides support for Landau notation for functions taking values in
topological vector spaces that do not carry norms. We may place ourselves in this situation as
follows:
```lean
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  (f g : α → E)
```
Without a norm, it is necessary to use the scalar action and so an alternative notation with room
to specify the scalars is required. The key definitions and notation are as follows:
- {name}`IsBigOTVS` with notation {lean}`f =O[𝕜; l] g`
- {name}`IsLittleOTVS` with notation {lean}`f =o[𝕜; l] g`

Critically, Mathlib knows that if one does have a norm, then {name}`IsBigOTVS` and {name}`IsBigO`
are equivalent:
```lean
example {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f g : α → E) :
    f =O[𝕜; l] g ↔ f =O[l] g :=
  isBigOTVS_iff_isBigO
```
Likewise Mathlib knows the corresponding little-o result {name}`isLittleOTVS_iff_isLittleO`.
