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

#doc (Manual) "H-spaces" =>

Recall that an H-space is a pointed topological space $`X` with a jointly continuous
multiplication map $`X × X → X`, often denoted $`(x, y) ↦ x ∧ y`. The distinguished
point $`e` acts as an identity up to homotopy in the sense that:
- $`e ∧ e = e`
- $`x ↦ x ∧ e` is homotopic to the identity (through maps fixing $`e`)
- $`x ↦ e ∧ x` is homotopic to the identity (through maps fixing $`e`)

In the sections which follow we outline how to discuss H-spaces in Mathlib.

# Defining an H-space

Mathlib contains a definition of H-spaces. To say that a type $`X` carries the structure
of an H-space one writes:
```lean
variable (H : Type*) [TopologicalSpace H] [HSpace H]
```
After opening the relevant scope:
```lean
open scoped HSpaces
```
special notation is available for the H-space multiplication:
```lean
variable (x y : H)
#check x ⋀ y
```

# Products

Mathlib knows that the product of two H-spaces is an H-space:
```lean
variable (H' : Type*) [TopologicalSpace H'] [HSpace H']

#synth HSpace (H × H')
```
Furthermore we can witness that the multiplication on the product is
what we expect as follows:
```lean
example (x y : H) (x' y' : H') :
    (x ⋀ y, x' ⋀ y') = (x, x') ⋀ (y, y') :=
  rfl
```

# Examples

## Topological groups

A topological group $`G` is an H-space. We can witness that Mathlib knows
this as follows:
```lean
variable (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

#synth HSpace G
```
Moreover we can witness that the H-space product is just the group product
as follows:
```lean
example (g h : G) :
    g * h = g ⋀ h := rfl
```

## Loops

If $`X` is a topological space, Mathlib knows that the space of loops based at
a point $`x` is an H-space (in the compact-open topology) with the expect product:
```lean
variable (X : Type*) [TopologicalSpace X] (x : X)

#synth HSpace (Path x x)

example (γ γ' : Path x x) :
  γ.trans γ' = γ ⋀ γ' := rfl
```
