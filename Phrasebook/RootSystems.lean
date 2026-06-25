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

#doc (Manual) "Root systems" =>

We describe Mathlib's theory of root systems and root data in the sections below.

# First examples

A root system is a finite collection of non-zero vectors in Euclidean space that is invariant
under reflection in the hyperplane perpendicular to any of the vectors. In fact, this data
determines the inner product up to scale and alternative definitions exist which obviate the need
to supply the inner product as part of the data. Mathlib omits the inner product, partly
because it allows a unified treatment of root systems and root data.

The following adds a root system to the Lean environment
```lean
variable {ι R M N : Type*} [Finite ι] [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsRootSystem]
```

Similarly, the following adds a root datum to the Lean environment
```lean
variable {ι M N : Type*} [Finite ι]
  [AddCommGroup M] [Module.Finite ℤ M]
  [AddCommGroup N] [Module.Finite ℤ N]
  (P : RootDatum ι M N)
```
Note that we do not need to add the assumption that $`M` and $`N` are free since
$`P` includes the data of a perfect pairing between $`M` and $`N` and, together with
finiteness, this ensures freeness. Indeed we can witness this as follows:
```lean
open Module in
example : Free ℤ M :=
  have : IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
  free_of_finite_type_torsion_free'
```

# Properties of root systems and root data

Mathlib contains API for numerous properties of root systems including:
- Being *reduced* {name}`RootPairing.IsReduced`
- Being *irreducible* {name}`RootPairing.IsIrreducible`
- Being *crystallographic* {name}`RootPairing.IsCrystallographic`

In addition the following concepts also all exist:
- *Morphisms* {name}`RootPairing.Hom`
- *Equivalences* {name}`RootPairing.Equiv`
- The *induced bilinear form* {name}`RootPairing.RootForm`
- The *Weyl group* {name}`RootPairing.weylGroup`
- The concept of a *base* {name}`RootPairing.Base` (aka a system of simple roots).

# Notable results

Some notable results and constructions contained in Mathlib are:
- Any root system over a field of characteristic zero has a base {name}`RootPairing.nonempty_base`
- A root system determines a Lie algebra {name}`RootPairing.GeckConstruction.lieAlgebra`, and this
  Lie algebra is semisimple:
  ```lean -show
  variable {ι K M N : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    [DecidableEq ι] [Fintype ι]
    [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    {P : RootPairing ι K M N}
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    {b : P.Base}
    [Fact ((4 - b.cartanMatrix).det ≠ 0)] -- TODO Drop this!
  open LieAlgebra
  ```
  ```lean
  #synth HasTrivialRadical K
    (RootPairing.GeckConstruction.lieAlgebra b)
  ```
