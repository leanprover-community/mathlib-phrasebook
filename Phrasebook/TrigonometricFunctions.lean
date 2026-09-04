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

#doc (Manual) "Trigonometric functions" =>

Mathlib contains definitions for the standard trigonometric
functions. We outline some related theory here.

To get some notation below we first open a scope:
```lean
open scoped Real
```

# Basic definitions

Mathlib contains each of the following definitions:
```lean
#check Complex.sin
#check Complex.cos
#check Complex.tan
```
For {name}`Complex.tan`, which has poles at $`± π / 2`, $`± 3π / 2`, $`± 5π / 2`,
the junk value $`0` is used:
```lean
open Complex in
example (k : ℤ) :
    tan (π / 2 + k * π) = 0 := by
  convert tan_int_mul_pi_div_two (2 * k + 1)
  grind
```

The hyperbolic variants are also available:
```lean
#check Complex.sinh
#check Complex.cosh
#check Complex.tanh
```
In addition, specialised variants over the real numbers exist:
```lean
#check Real.sin
#check Real.cos
#check Real.tan
```
as well as the "inverse" functions over the reals:
```lean
#check Real.arcsin
#check Real.arccos
#check Real.arctan
```

# Basic properties

Mathlib knows the various relationships between the trigonometric functions
and the exponential. For example:
```lean
open Complex in
example (z : ℂ) :
    cos z = (exp (z * I) + exp (-z * I)) / 2 :=
  rfl
```
We note in passing that Mathlib also contains a more general definition of
exponential {name}`NormedSpace.exp` which allows more general scalars, but
the trigonometric functions are only defined for the reals and complexes.

Mathlib also knows about the relevant periodicity. For example:
```lean
open Complex in
example (z : ℂ) :
    sin (z + 2 * π) = sin z :=
  sin_add_two_pi z
```
Finally Mathlib knows that these are analytic functions:
```lean
open Complex in
example (z : ℂ) :
    AnalyticAt ℂ sin z :=
  analyticAt_sin
```
and facts about their derivatives such as:
```lean
open Complex in
example (z : ℂ) :
    deriv sin = cos :=
  deriv_sin
```

# Special values and identities

```lean
open Real
variable {x : ℝ}
```

Many basic facts about the trigonometric functions are also known,
including special values such as:
```lean
example :
    sin (π / 4) = √2 / 2 :=
  sin_pi_div_four

example :
    cos (π / 3) = 1 / 2 :=
  cos_pi_div_three

example :
    cos (π / 5) = (1 + √5) / 4 :=
  cos_pi_div_five

example :
    cos (π / 8) = √(2 + √2) / 2 :=
  cos_pi_div_eight

example :
    tan (π / 4) = 1 :=
  tan_pi_div_four

example :
    tan (π / 6) = 1 / √3 :=
  tan_pi_div_six
```

and identities such as:
```lean
example :
    cos (2 * x) = 2 * cos x ^ 2 - 1 :=
  cos_two_mul x

example :
    sin (2 * x) = 2 * sin x * cos x :=
  sin_two_mul x

example :
    cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x :=
  cosh_three_mul x
```
and bounds such as:
```lean
example (hx : |x| ≤ 1) :
    |cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 * (5 / 96) :=
  cos_bound hx

example (hx : |x| ≤ 1) :
    |sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 100 :=
  sin_bound hx
```
