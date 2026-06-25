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

#doc (Manual) "Covering spaces" =>

We outline some features of Mathlib's covering space theory in the sections below.

# Basic setup

The following code expresses the fact that a map $`f : E → X` between topological spaces is a
covering map:
```lean
variable (E X : Type*)
  [TopologicalSpace E] [TopologicalSpace X]
  (f : E → X) (hf : IsCoveringMap f)
```
We may witness that this is defined using the expected property {name}`IsEvenlyCovered` as follows:
```lean
example {g : E → X} :
    IsCoveringMap g ↔
      ∀ x, IsEvenlyCovered g x (g ⁻¹' {x}) :=
  Iff.rfl
```
Mathlib knows numerous facts about covering maps, including that they are:
- *Continuous*: {name}`IsCoveringMap.continuous`
- *Open*: {name}`IsCoveringMap.isOpenMap`
- *Local homeomorphisms*: {name}`IsCoveringMap.isLocalHomeomorph`
- *Quotient maps*: {name}`IsCoveringMap.isQuotientMap`
- *Separated maps*: {name}`IsCoveringMap.isSeparatedMap`

Mathlib also has API to support the situation when a map is only a covering map over some subset of
the the base (this allows support for branched coverings). This is captured in {name}`IsCoveringMapOn`
and the related API.

# Constructing covering maps

Mathlib contains API for constructing covering maps in various situations.

## Locally trivial maps with discrete fibers.

If $`f : E → X` is locally trivial with discrete fibers then the lemma
{name}`IsFiberBundle.isCoveringMap` demonstrates that $`f` is a covering map. This uses
the same definition {name}`Bundle.Trivialization` as Mathlib's fiber bundle theory.

An convenience variant of this also exists as {name}`FiberBundle.isCoveringMap` in which the
{name}`FiberBundle` definition is used.

## Closed local homeomorphisms with finite fibers

If $`E` is Hausdorff, a sufficient condition for $`f : E → X` to be a covering map is that it is a
closed, local homeomorphism, with finite fibers. Mathlib knows this fact as
{name}`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`.

## Local homeomorphims from a compact space

If $`E` is compact and Hausdorff and $`X` is Hausdorff, then a map $`f : E → X` is a local
homeomorphism iff it is a covering map. Mathlib knows this fact as
{name}`isLocalHomeomorph_iff_isCoveringMap`.

# Quotient by properly discontinuous, free group actions

Covering spaces arise from group actions and Mathlib has API to support this. A key concept is that
of quotient covering map. If a group $`G` acts on $`E` and $`f : E → X` then we say $`f` is a
quotient covering map if:
- $`f` is a quotient map whose fibres are the orbits of $`G` (i.e., it is a quotient map for the action of $`G`)
- $`G` acts by homeomorphims
- every point of $`E` has a neighborhood whose translates by the group elements are pairwise
  disjoint

This is the definition {name}`IsQuotientCoveringMap`. Included in the API for such maps are the
following facts:
- Quotient covering maps are covering maps {name}`IsQuotientCoveringMap.isCoveringMap`
- If $`G` acts freely and properly discontinuously by homeomorphisms on a locally compact Hausdorff
  space then we have a quotient covering map
  {name}`Topology.IsQuotientMap.isQuotientCoveringMap_of_properlyDiscontinuousSMul`.
- If $`E` is simply connected and $`f` is a quotient covering map, then the fundamental group of
  $`X` is $`G`, {name}`IsQuotientCoveringMap.fundamentalGroupEquiv`.
