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

#doc (Manual) "Hausdorff Measure" =>

We describe Mathlib's theory of Hausdorff measure and Hausdorff dimension in the sections below.

For convenience we begin by opening namespaces:
```lean
open MeasureTheory MeasureTheory.Measure
```

# Basic construction

A metric space $`X` carries a natural measurable space structure, the Borel $`σ`-algebra,
and for each non-negative real number $`d`, a measure, the $`d`-dimensional Hausdorff measure.


Mathlib contains a theory of Hausdorff measure. Here is how it looks:
```lean
variable (X : Type*)
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (d : ℝ)

#check hausdorffMeasure (X := X) d
```
Note that $`d` can be any real number but the definition should be regarded as junk
when $`d < 0`.

Mathlib also has special notation for the Hausdorff measure. It is available here
because we opened the `MeasureTheory` namespace above:
```lean
#check (μH[d] : Measure X)
```

# Normalisation

The informal mathematical literature contains differing conventions for the overall scale
of the Hausdorff measure. Mathlib's definition uses the _unnormalised_ convention. This can
be seen by the absence of any scale factors in the formula appearing in
{name}`hausdorffMeasure_apply`: the measure is just an infimum of sums of powers of diameters.

Another way to witness the choice of scaling is to note that in $`\mathbb{R}^n` with the sup norm,
the unit cube has measure 1 for the $`n`-dimensional Hausdorff measure:
```lean
open Fintype Set in
example {n : ℕ} :
    μH[n] (Icc 0 1 : Set (Fin n → ℝ)) = 1 := by
  have : (n : ℝ) = card (Fin n) := by rw [card_fin]
  simp [this, Real.volume_Icc_pi]
```

# Connection to Lebesgue and Haar

In Mathlib, the real numbers carry the Lebesgue measure as their canonical measure.
It is called {lean}`(volume : Measure ℝ)`. Mathlib knows that this coincides with the
1-dimensional Hausdorff measure and we can witness this as follows:
```lean
example :
    μH[1] = (volume : Measure ℝ) :=
  hausdorffMeasure_real
```

More generally, Mathlib knows that the Hausdorff measure may be a Haar measure.
For example if $`E` is a finite-dimensional normed real vector
space then Mathlib knows that the top-dimensional Hausdorff measure is a Haar measure:
```lean
open Module in
example {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    IsAddHaarMeasure (G := E) μH[finrank ℝ E] :=
  inferInstance
```

# Hausdorff dimension

Mathlib also contains a theory of Hausdorff dimension. It is called {name}`dimH`.

Given a subset $`s` of a metric space $`X`, its Hausdorff dimension can be defined
as the supremum of dimensions such that the correpsonding Hausdorff measure is
infinite. Mathlib knows this:
```lean
open ENNReal NNReal in
example (s : Set X) :
    dimH s = ⨆ (d : ℝ≥0) (_ : μH[d] s = ∞), (d : ℝ≥0∞) :=
  dimH_def s
```
Alternatively the Hausdorff dimension can be defined as the infimum of dimensions
such that the corresponding Hausdoff measure is zero. Mathlib knows this too:
```lean
open ENNReal NNReal in
example (s : Set X) :
    dimH s = ⨅ (d : ℝ≥0) (_ : μH[d] s = 0), (d : ℝ≥0∞) :=
  dimH_eq_iInf s
```
