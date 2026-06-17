/-
Copyright (c) 2026 Li Xuanji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

open Verso.Genre Manual

open Verso.Genre.Manual.InlineLean


open Phrasebook

set_option pp.rawOnError true

#doc (Manual) "How to write standard group actions using Mathlib" =>

This page assumes you have already read the [Mathematics in Lean section about group actions](https://leanprover-community.github.io/mathematics_in_lean/C09_Groups_and_Rings.html#group-actions).

# The left multiplication action

:::leanSection
```lean -show
variable {G X : Type*} [Monoid G] (g : G) (x : X) [MulAction G X]
```

As mentioned in Mathematics in Lean, the typeclass {lean}`MulAction G X` allows us to write {lean}`g • x` for the action of a group element `g : G` on an element `x : X`. Given types `G` and `X`, only one action can be inferred (since we need an unambiguous value for {lean}`g • x`). In the case where the literature has multiple actions, one of them is chosen as the default action. For instance, given `G = X` and `[Group G]` the action of `G` on itself by left multiplication is chosen as the default action.

```lean
example {G} [Group G] (g s : G) : g • s = g * s :=
 smul_eq_mul g s
```
:::

# The conjugation action

:::leanSection
```lean -show
variable {G X : Type*} [Monoid G] (g : G) (x : X) [MulAction G X]
```

To write different actions, we use type synonyms. The type {lean}`ConjAct G` is a type synonym for `G`; a term of type {lean}`ConjAct G` contains exactly the same data as a term of type `G`, and can be converted to `G` using the function {name}`ConjAct.ofConjAct`.

This allows us to have elements of {lean}`ConjAct G` act on `G` by conjugation.

```lean
open ConjAct in
example {G} [Group G] (g : ConjAct G) (s : G) :
    g • s = ofConjAct g * s * (ofConjAct g)⁻¹ :=
  smul_def g s
```
:::

# The left multiplication action on subsets

:::leanSection
```lean -show
variable {G X : Type*} [Monoid G] (x : X) [MulAction G X]
```

A group acts on its subsets by left multiplication. Recall that given a group structure {lean}`Group G` on a type `G`, the type of subsets of `G` is {lean}`Set G`. Mathlib provides an instance {name}`Set.mulActionSet` `:` {lean}`MulAction G (Set G)` for this action, and notation `g • S` for the action of `g : G` on `S : Set G`, which is enabled in the `Pointwise` namespace.

```lean
open scoped Pointwise
open DihedralGroup

def S : Set (DihedralGroup 3) := {.r 0, .r 1}
def g : DihedralGroup 3 := .r 0
example : g • S = {.r 0, .r 1} := by
  simp [g, S]
```

:::
