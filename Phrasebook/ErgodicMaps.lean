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

#doc (Manual) "Working with ergodic maps in Mathlib" =>

# Ergodic maps

Given a map `f : α → α` where `α` is a measurable space, equipped with a measure `μ`,
one says `f` is ergodic if:
- `f` is measurable (see {name}`Measurable`)
- `f` is measure-preserving (see {name}`MeasureTheory.MeasurePreserving`)
- the only `f`-invariant sets are almost empty or full (see {name}`PreErgodic`)

The following adds an ergodic map to the Lean environment
```lean
variable {α : Type*}
  [MeasurableSpace α] (μ : MeasureTheory.Measure α)
  {f : α → α} (hf : Ergodic f μ)
```

Mathlib also contains a definition of the weaker concept of quasi-ergodic maps. This
weakens the measure-preserving axiom to quasi-measure-preserving
(see {lean}`@MeasureTheory.Measure.QuasiMeasurePreserving`)

The following adds a quasi-ergodic map to the Lean environment
```lean
variable {α : Type*}
  [MeasurableSpace α] (μ : MeasureTheory.Measure α)
  {f : α → α} (hf : QuasiErgodic f μ)
```

# Examples

Mathlib contains proofs that certain maps are ergodic. Here are two examples of maps
on the circle $`\mathbb{R} / \mathbb{Z}`:
1. Given given a natural number $`n > 1`, the map $`x ↦ nx` is ergodic.
   This appears in Mathlib as {name}`AddCircle.ergodic_nsmul`.
1. Given a point $`a`, the map $`x ↦ x + a` is ergodic iff $`a` is has infinite order
   (i.e., is irrational).
   This appears in Mathlib as {name}`AddCircle.ergodic_add_right`.
