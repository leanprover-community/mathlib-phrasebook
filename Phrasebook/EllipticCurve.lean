/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
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

#doc (Manual) "Tutorial: How to work with elliptic curves using Mathlib" =>

The phrase "elliptic curve" means different things to different people. This
tutorial discusses the basic algebraic theory of elliptic curves, via the
classical approach: cubic equations in two variables.

By the end of this tutorial, you should be able to

* Define an elliptic curve over a field in mathlib;
* Create points on elliptic curves;
* Add and negate the points, and more generally use the group law on the
  points of the curve.
* Create the Tate module of an elliptic curve

Let's get started!

# Making an affine Weierstrass curve.

Let $`K` be a field. An _affine Weierstrass curve_ over $`K` is a certain kind of cubic equation
in two variables, for example $`Y^2=X^3+1` or $`Y^2+Y=X^3-37X`. The general form
of this equation is

$`Y^2+a_1XY+a_3Y=X^3+a_2X^2+a_4X+a_6`

where $`a_1, a_2, a_3, a_4, a_6` are elements of $`K` (note:
the absence of $`a_5` is a feature, not a typo). The reason
we use the "long Weierstrass form" rather than the perhaps
more traditional $`Y^2=X^3+AX+B` is that the long form works
for fields of all characteristics, and mathlib typically strives
for maximal generality.

Here is an example of how to make an affine Weierstrass curve in Lean.

::: leanSection
```lean
open WeierstrassCurve
/-
The Weierstrass curve Y² + iXY = X³ - π over the
complex numbers.
-/
noncomputable example : Affine ℂ := {
  a₁ := Complex.sqrt (-1)
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := Real.pi
}
```

Instead of explicitly writing this longhand,
we can simply create a Weierstrass curve with
a 5-tuple of field elements. Here is an example of this:

```lean
/-
The elliptic curve Y² + Y = X³ - X over ℚ
(this is the curve "37A1" a.k.a.
https://www.lmfdb.org/EllipticCurve/Q/37/a/1 in the
L-functions and modular forms database.
-/
def E37A1 : Affine ℚ := ⟨0, 0, 1, -1, 0⟩
```

The Weierstrass curve $`Y² = X³` (over the reals, say)
has a singular point at the origin, because $`Y² - X³` and
its derivaties with respect to $`X` and $`Y` all vanish at
the origin, and this is fine.

```lean
/-
A Weierstrass curve can have singular points.
-/
example : Affine ℝ := ⟨0, 0, 0, 0, 0⟩
```
:::

# Making an elliptic curve

An _elliptic curve_ over a field is a nonsingular affine Weierstrass curve.
It turns out that nonsingularity is equivalent to nonvanishing of
a certain polynomial in the $`a_i`, namely the discriminant of the $`a_i`.
We express nonsingularity with the `WeierstrassCurve.IsElliptic` class as follows.

::: leanSection
```lean
open WeierstrassCurve
/-
recall that we defined `E37A1 : Affine ℚ`
to be the curve `Y² + Y = X³ - X` over `ℚ`.
Now let's show that this is an elliptic curve.
-/
instance : WeierstrassCurve.IsElliptic E37A1 := {
  isUnit := by
    -- ⊢ IsUnit (Δ E37A1)
    rw [isUnit_iff_ne_zero]
    -- ⊢ Δ E37A1 ≠ 0
    decide +kernel
}
```

This proof works because `Δ E37A1` definitionally unfolds to
an explicit rational number, and so Mathlib's `decide` tactic will work
because the rationals have decidable equality. For a curve
over the reals, one has to work a little harder:

```lean
def E_real : Affine ℝ := ⟨0, 0, 1, -1, 0⟩
instance : WeierstrassCurve.IsElliptic E_real := {
  isUnit := by
    -- ⊢ IsUnit (Δ E_real)
    rw [isUnit_iff_ne_zero]
    -- ⊢ Δ E_real ≠ 0
    unfold Δ
    -- ⊢ -b₂ E_real ^ 2 * b₈ E_real - 8 * b₄ E_real ^ 3
    -- - 27 * b₆ E_real ^ 2 + 9 * b₂ E_real * b₄ E_real
    -- * b₆ E_real ≠ 0
    unfold E_real b₂ b₄ b₆ b₈ a₁ a₂ a₃ a₄ a₆
    -- a mess
    dsimp only
    -- (some explicit real number) ≠ 0
    norm_num
}
```

The `norm_num` tactic can be used to do computations with
real numbers. There should really be a tactic which does all of this
unfolding for you; this would make working with
elliptic curves a little easier. In fact perhaps there
should simply be a lemma which says `Δ E = (the explicit formula)`
so we would just be able to rewrite this lemma and then
apply `norm_num`.

Because `IsElliptic` is a class, this is the way to
say "let $`K` be a field and let $`E` be an
elliptic curve over $`K`":

```lean
variable (K : Type*) [Field K]
    (E : Affine K) [WeierstrassCurve.IsElliptic E]
```
:::

# Points on an elliptic curve

Let $`E` be an elliptic curve over a field.

::: leanSection
```lean
open WeierstrassCurve
variable (K : Type*) [Field K]
    (E : Affine K) [WeierstrassCurve.IsElliptic E]
```

The _points_ of $`E` are of two forms: either solutions $`(x,y)` to the
equation with $`x` and $`y` in $`K`, or the "point at infinity".
A standard result is that the points on the curve naturally form
an additive abelian group, and this result is in `mathlib`.
However, the definition of addition is computable, which gives
us a "gotcha" -- one has to assume that the field $`K` has
decidable equality in order to access the group law.

```lean
-- necessary to access the group law
variable [DecidableEq K]

variable (P Q R : E.Point)
#check P + Q -- E.Point
#check P - Q -- E.Point
#synth AddCommGroup E.Point -- works
-- associativity of the group law is a theorem of mathlib.
-- See https://arxiv.org/abs/2302.10640
example : (P + Q) + R = P + (Q + R) := add_assoc _ _ _
```

For an explicit elliptic curve over an explicit field,
one can construct explicit points. Here however there
is a theorem to be proved, namely that the coordinates
do indeed satisfy the equation. Here is an example,
making the point $`(x,y)=(6,14)` on E37A1:
using the constructor `WeierstrassCurve.Affine.Point.mk`.
We've already opened `WeierstrassCurve`; let's also
open `Affine` so that we can just refer to this function
as `Point.mk`.

```lean
open Affine
example : E37A1.Point := Point.mk (x := 6) (y := 14) sorry

```

Right now `x` and `y` are implicit inputs to `Point.mk` so
we have to supply them using `(x := _)` and `(y := )`.
But what is the `sorry`? Of course, this is the proof that
the point is on the curve. Let's fill it in:

```lean
def P37 : E37A1.Point := Point.mk (x := 6) (y := 14) <| by
  -- ⊢ E37A1.Equation 6 14
  rw [equation_iff]
  -- (goal is now an explicit identity between rationals)
  decide +kernel
```

Once we have constructed this point, we can use Lean as a simple
computer algebra system and add the point to itself or
to other points.

```lean
#eval P37 + P37
-- WeierstrassCurve.Affine.Point.some
-- (1357 : Rat)/841 (28888 : Rat)/24389 _

def Q37 : E37A1.Point := Point.mk (x := 2) (y := 2) <| by
  rw [equation_iff]
  decide +kernel

#eval P37 + Q37
-- WeierstrassCurve.Affine.Point.some
-- 1 0 _

-- Let's evaluate P37 - P37
#eval P37 - P37
-- WeierstrassCurve.Affine.Point.zero
-- That evaluation relies on trusting
-- Lean's compiler.

-- Let's now prove that it's zero,
-- using only the kernel.
example : P37 - P37 = 0 := by simp
```

We can recover the $`X`-coordinate of a point on an elliptic curve
using `Point.xRep`; this returns `![x,1]` if the $`X`-coordinate
is $`x`, and `![1,0]` (the point at infinity in `ℙ¹`) otherwise.

```lean
example : P37.xRep = ![6, 1] := by
  rfl -- true by definition
example : (P37 - P37).xRep = ![1, 0] := by
  simp -- `simp` simplifies `P37 - P37` to `0`
  -- and then the result is true by definition.
```
:::

# The Galois action on points of an elliptic curve

Let $`K` be a field and let $`E` be an elliptic curve over $`K`.

::: leanSection
```lean
open WeierstrassCurve Affine
variable (K : Type*) [Field K]
    (E : Affine K) [WeierstrassCurve.IsElliptic E]
```

Let $`L` be a field extension of $`K` (typically it taken to be
an algebraic or separable closure of $`K`, but any field extension
of $`K` will work)

```lean
variable (L : Type*) [Field L] [Algebra K L]
```

The base change of $`E` to $`L` is denoted by `E⁄k`. Here the
forward-slash is not the usual `/` key on your keyboard, but
a unicode character which you can get in Lean by writing
`\textfractionsolidus` or just `\textf` for short.

```lean
#check E⁄L -- E⁄L : Affine L
```

If $`n` is a natural number then the $`n`-torsion in the points of `E⁄L` is a group
(assuming $`L` has decidable equality), and we can look at the $`n`$-torsion in this group.

```lean
variable (n : ℕ) [DecidableEq L]
#check Submodule.torsionBy ℤ (E⁄L).Point n
```

This torsion subgroup has size at most $`n^2`, although this still has not been formalized
in Lean yet (David Ang and Junyan Xu are developing a theory of division polynomials which
will have this as a consequence). What we do have is functoriality of the $`L`-points
with respect to $`K`-automorphisms of $`L` (which Lean denotes `L ≃ₐ[K] L`):

```lean
noncomputable example (g : L ≃ₐ[K] L) :
    (E⁄L).Point →+ (E⁄L).Point :=
  Point.map (g : L →ₐ[K] L)
```

This action is not registered as an instance, but we can register it now.

```lean
noncomputable instance : SMul (L ≃ₐ[K] L) (E⁄L).Point := {
  smul g P := Point.map (g : L →ₐ[K] L) P
}
```

We can even check that this makes the $`L`$-points of $`E`
into a module for the group `L ≃ₐ[K] L` of $`K`-algebra
automorphisms of $`L`. We will need to check the axioms,
but the proofs are already in `mathlib`.

```lean
noncomputable instance :
    DistribMulAction (L ≃ₐ[K] L) (E⁄L).Point where
      one_smul P := Point.map_id P
      mul_smul g h P := (Point.map_map
        (h : L →ₐ[K] L) (g : L →ₐ[K] L) P).symm
      smul_zero g := rfl
      smul_add g := map_add _
```

The Galois action on the points (we call it a Galois action
even though we have not assumed anything about $`L/K` being
algebraic, normal or separable!) induces an action
of $`{\mathrm{Aut}}_K(L)` on the $`n`-torsion points
for all $`n`. We skip the proofs for now.

```lean
noncomputable instance (n : ℕ) :
    DistribMulAction (L ≃ₐ[K] L)
      (Submodule.torsionBy ℤ (E⁄L).Point n) := {
  smul g P := ⟨g • P, sorry⟩
  mul_smul := sorry
  one_smul := sorry
  smul_zero := sorry
  smul_add := sorry
    }
```

As an exercise, one could now glue these actions together to
define a continuous action of the Galois group on the Tate module
of an elliptic curve. Right now most of this material is
in the FLT project, but has not been upstreamed,
so the easiest approach here is to simply wait until the material
finds its way into `mathlib`.
:::
