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

#doc (Manual) "Topological vector spaces" =>

We describe Mathlib's theory of topological vector spaces in the sections below. The theory
supports a broad class of coefficients, including $`ℝ`, $`ℂ`, $`ℚ_p` (the p-adics).

# General topological vector spaces

```lean -show
section Temporary
```

The following code adds a TVS called $`E` with coefficients in the normed field $`𝕜`
to the Lean environment:
```lean
variable (E 𝕜 : Type*) [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul 𝕜 E]
```
Since such a space is a topological group:
```lean
example : IsTopologicalAddGroup E :=
  { continuous_neg := by
      convert! continuous_const_smul (-1 : 𝕜) (T := E)
      ext; simp }
```
we could also assume {name}`IsTopologicalAddGroup` instead of {name}`ContinuousAdd` but
we usually make the superficially weaker assumption.

```lean -show
end Temporary
```

# Locally convex spaces

```lean -show
section Temporary
```

Locally convex topological vector spaces (LCTVS) come in different forms. Mathlib distinguishes
between the topological notion and spaces whose topology is induced by a family of seminorms, and
the later one comes in two different forms. Hence, we have the options
- {name}`LocallyConvexSpace`
- {name}`WithSeminorms`
- {name}`PolynormableSpace`

Mathlib contains an extensive theory of all of these different notions. We will now describe how
and when to use which notion.

The first option, {name}`LocallyConvexSpace`, is the topological characterization that the convex
neighborhoods of a point form a neighborhood basis of that point and this can be combined
with the above characterization of TVS to spell a CLTVS over `ℝ` or `ℂ` as follows:
```lean
variable (E 𝕜 : Type*) [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  [NormedSpace ℝ 𝕜] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [LocallyConvexSpace ℝ E]
```
This spelling is useful for proving topological properties about LCTVS.
```lean -show

end Temporary
section Temporary
```
The more analytical characterization of LCTVS is that the topology is induced by a family of seminorms
and there is the predicate {name}`WithSeminorms` that states that a given topology is induced by
a family of seminorms:

```lean
variable {ι : Type*} (E 𝕜 : Type*) [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
```
and Mathlib knows that in this case the space is locally convex:
```lean
example
    [NormedSpace ℝ 𝕜] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
```
```lean -show
end Temporary
section Temporary
```
and conversely the {name}`gaugeSeminormFamily` induces the topology on a locally convex space:
```lean
open scoped ComplexOrder
variable {E 𝕜 : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace 𝕜 E]
example : WithSeminorms (gaugeSeminormFamily 𝕜 E) :=
  with_gaugeSeminormFamily
```

The spelling {name}`WithSeminorms` is used in the case where the family of seminorms explicitly
appears in the statement or the hypothesis, for example {name}`WithSeminorms.tendsto_nhds_atTop`.

```lean -show
end Temporary
section Temporary
```
Finally, there is {name}`PolynormableSpace`, which states that the family of continuous seminorms
induce the topology.
```lean
variable {E 𝕜 : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [PolynormableSpace 𝕜 E]
```
This characterization of LCTVS is valid for coefficients more general than $`ℝ` or $`ℂ`
and coincides with {name}`LocallyConvexSpace` if the base field is $`ℝ` or $`ℂ`.

```lean
open scoped ComplexOrder

variable (E 𝕜 : Type*) [RCLike 𝕜]
  [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  [Module ℝ E] [ContinuousSMul ℝ E]
  [IsScalarTower ℝ 𝕜 E]

example [LocallyConvexSpace 𝕜 E] :
    PolynormableSpace 𝕜 E := by
  infer_instance

example [PolynormableSpace ℝ E] :
    LocallyConvexSpace ℝ E := by
  infer_instance
```

Using {name}`PolynormableSpace` is preferred over {name}`WithSeminorms` when the family of
seminorms does not explicitly appear in either the hypothesis or the conclusion, for instance
for statements about derivatives of Fréchet-valued functions.

```lean -show
end Temporary
```

## Notable results
* The *Hahn-Banach theorem*: {name}`StrongDual.exists_extension`
* The *Banach-Steinhaus theorem*: {name}`WithSeminorms.banach_steinhaus` and
  {name}`PolynormableSpace.banach_steinhaus`

# Banach and Hilbert spaces

To add a Banach space to the environment one writes:
```lean -show
section Temporary
```

```lean
variable (E 𝕜 : Type*) [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]
```
Special notation for the norm is available for vectors in a Banach
space:
```lean
example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
```
```lean -show
end Temporary

section Temporary
```
For a Hilbert space one writes:
```lean
variable (E 𝕜 : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
```
Special notation for the inner product is available for vectors in a Hilbert
space after opening the `InnerProductSpace` scope:
```lean
open scoped InnerProductSpace

example (x y : E) :
    ⟪x + y, x + y⟫_𝕜 + ⟪x - y, x - y⟫_𝕜 =
      2 * (⟪x, x⟫_𝕜 + ⟪y, y⟫_𝕜) :=
  parallelogram_law
```
```lean -show
end Temporary
```

## Notable results

The following are some notable results in Mathlib's theory library of topological
vector spaces:
- The *open mapping theorem*: {name}`ContinuousLinearMap.isOpenMap`
- The *Hahn-Banach theorem*: {name}`exists_extension_norm_eq`
- The *Lax-Milgram theorem*: {name}`IsCoercive.continuousLinearEquivOfBilin`
- The *Banach-Steinhaus theorem*: {name}`banach_steinhaus`
- The *Riesz representation theorem*: {name}`InnerProductSpace.toDual`
- The *Banach-Alaoglu theorem*: {name}`WeakDual.isCompact_polar`

# Continuous linear maps

```lean -show
section Temporary
```

If $`E` and $`F` are two topological vector spaces:
```lean
variable (𝕜 E F : Type*) [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousSMul 𝕜 F]
```
we can speak of the continuous linear maps between $`E` and $`F`. The relevant definition is
{name}`ContinuousLinearMap` and it has special notation as follows:
```lean
#check E →L[𝕜] F
```

```lean -show
end Temporary
section Temporary
```

## Topologies on continuous linear maps

The space of continuous linear maps is naturally equipped with topology of *bounded* convergence.
This topology coincides with the operator norm topology in case linear maps on Banach spaces.


```lean
variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E →L[𝕜] F)

example (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x

example {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
    ‖f‖ ≤ M := f.opNorm_le_bound hMp hM
```

Mathlib also knows about the following topologies:

- *Pointwise convergence* (or strong operator topology): {name}`PointwiseConvergenceCLM`
- *Compact convergence*: {name}`CompactConvergenceCLM`
- *Weak operator topology*: {name}`ContinuousLinearMapWOT`

## Topological dual

In the special case that $`F` is the base field $`𝕜`, we have the abbreviation {lean}`StrongDual 𝕜 E`
for the {lean}`E →L[𝕜] 𝕜`. This space naturally carries the topology of bounded convergence, which
is also known as the strong topology. To obtain the weak dual use {name}`WeakDual`.

```lean -show
end Temporary
```
