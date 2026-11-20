/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib
import Phrasebook.Meta.Lean
import VersoManual

open Phrasebook
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Category theory" =>

This page explains how to express common concepts in category theory
using the definitions in Mathlib.
We assume basic knowledge of both Lean and category theory.

Most of the definitions regarding general category theory are in
the `CategoryTheory` namespace. In order to use limits or colimits,
we often need to open the `CategoryTheory.Limits` sub-namespace.
A typical file using category theory may contain:

```lean
open CategoryTheory Limits
```

The exposition is split in the following subsections:

# Categories

A category involves a notion of objects, a notion of morphisms
between two such objects, a distinguished morphism from any object to
itself (the identity), the composition law of morphisms, and a few axioms.
In Mathlib, a category is thought as a structure on the type
of objects, and this structure involves a typeclass `Category`.

If we need to declare a category `C` as a variable, introduce
three objects `X`, `Y`, `Z`, two composable morphisms `f` from `X` to `Y`
and `g` from `Y` to `Z`, and consider the composition of `f` and `g`,
we proceed as follows:
::: leanSection
```lean
variable {C : Type*} [Category* C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

example : X ⟶ Z := f ≫ g -- type `≫` as `\gg`
```
The arrow `⟶` that is used to denote the type of morphisms in a
category `C` is typed as `\hom` and it is different from the basic arrow `→`
(typed as `\to`) used for the type of nondependent functions between two types.

Note that the composition denoted here `f ≫ g` would usually be denoted "gf"
in the mathematical literature. Getting used to this notation is a
*rite of passage*. Beware that you may experience trouble going back to
the "gf" notation if you do too much formalization of category theory
in Lean.

The identity of an object `X` is denoted `𝟙 X` (type `𝟙` as `\b1`):
```lean
example : f ≫ 𝟙 Y = f := by simp
example : 𝟙 X ≫ f = f := by simp
```
:::

About universes, we may observe that in this implementation,
the types of morphisms in a category `C` (with `C : Type u`) can be
considered as a dependent function `C → C → Type v`: for each `X : C`
and `Y : C`, the type `X ⟶ Y` of morphisms from `X` to `Y`
belongs to `Type v` for a certain universe `v`. If we need to be specific
about these two universe parameters `u` (for objects) and
`v` (for morphisms), we do:
::: leanSection
```lean
universe v u -- `v` purposely appears first
variable {C : Type u} [Category.{v} C]
```
:::
Otherwise, `variable {C : Type*} [Category* C]` would register
two fresh arbitrary universes. Declaring a `u`-small category
can be done as
::: leanSection
```lean
variable {C : Type u} [SmallCategory C]
  -- this is equivalent to `[Category.{u} C]`
```
:::


A few examples of categories will be discussed in this phrasebook. One of
the basic examples is the category structure induced by a preorder. The
definitions `homOfLE` and `leOfHom` can be used in order to transform
an inequality `h : a ≤ b` into a morphism `a ⟶ b` in the category of
a preorder, and vice versa:
::: leanSection
```lean
variable {α : Type*} [Preorder α]
#synth SmallCategory α

example {a b : α} (h : a ≤ b) : a ⟶ b := homOfLE h
example {a b : α} (f : a ⟶ b) : a ≤ b := leOfHom f

```
:::

If `C` is a category, the opposite category is denoted `Cᵒᵖ`:
::: leanSection
```lean
variable {C : Type*} [Category* C]

open Opposite

example (X : C) : Cᵒᵖ := op X
example (X : Cᵒᵖ) : C := X.unop
example {X Y : C} (f : X ⟶ Y) : op Y ⟶ op X := f.op
example {X Y : Cᵒᵖ} (f : X ⟶ Y) : Y.unop ⟶ X.unop := f.unop
```
:::
The objects of `Cᵒᵖ` (and also the morphisms in `Cᵒᵖ`) are
implemented as a 1-field structure `Opposite`: we do not want
to enforce `Cᵒᵖ = C`, because it would create a confusion
about which `Category` instance on this type should be used.
Note that the type `Cᵒᵖᵒᵖ` is not equal to `C` either!

# Associativity of the composition

::: leanSection
```lean -show
variable {C : Type*} [Category* C]
```

The composition of morphisms in a category is associative. When a term
is a composition of more than two morphisms, the syntax is set up so that
`f ≫ g ≫ h` means `f ≫ (g ≫ h)`, and this is also the `simp` normal form
(i.e. `(f ≫ g) ≫ h` simplifies to `f ≫ g ≫ h`):
```lean
variable {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

example : f ≫ g ≫ h = f ≫ (g ≫ h) := rfl
example : (f ≫ g) ≫ h = f ≫ g ≫ h := Category.assoc f g h
```

In non-formalized mathematics, the associativity of the composition
is often used implicitly. In formalized mathematics, we need to take
care about this associativity in one way or another when proving equalities
of morphisms:

```lean
variable {X₀ X₁ X₂ X₃ X₄ : C} (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂)
  (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄) (φ : X₁ ⟶ X₃)
  (h : f₁ ≫ f₂ = φ)

example : f₀ ≫ f₁ ≫ f₂ ≫ f₃ = f₀ ≫ φ ≫ f₃ := by
  rw [← Category.assoc f₁ f₂ f₃, h]
```

This proof uses the associativity in order to make the term `f₀ ≫ (f₁ ≫ f₂) ≫ f₃`
appear, which allows to rewrite `h`. Proceeding like this would be very unpractical
in more intricate cases, and it is also inconvenient because this would often
require using `Category.assoc` explicitly in both forward and backwards directions.
As it is a `simp` lemma, it is recommended to use it explicitly only in the forward direction.

An alternative proof can be obtained using specialized tactics:
```lean
example : f₀ ≫ f₁ ≫ f₂ ≫ f₃ = f₀ ≫ φ ≫ f₃ := by
  slice_lhs 2 3 => rw [h]
```
`slice_lhs` (and `slice_rhs`) are specialized `conv`-like tactics
which allow to zoom on certain chunks in the middle of compositions
of multiple morphisms. When there is no better way, this method
can be used when dealing with very long compositions.

In this case, the preferred proof would be:
```lean
example : f₀ ≫ f₁ ≫ f₂ ≫ f₃ = f₀ ≫ φ ≫ f₃ := by
  rw [reassoc_of% h]
```
This proof uses the term elaborator `reassoc_of%`: from an
an equality like `h : f₁ ≫ f₂ = φ`, it produces
a term `f₁ ≫ f₂ ≫ α = f₂ ≫ α` for a generic morphism `α`,
and it can be used in rewrites. Note that we do not need
the "dual" construction of a term `β ≫ f₁ ≫ f₂ = β ≫ f₂`
because `h` can be directly rewritten in it. Indeed,
this `reassoc_of% h` term could be rewritten in an
arbitrary composition like `β₀ ≫ ... ≫ βₙ ≫ f₁ ≫ f₂ ≫ γ₀ ≫ ... ≫ γₘ`
as soon as the list `[γ₀, ..., γₘ]` is nonempty.

Similarly, we have a `@[reassoc]` attribute (often used
in combination with `simp` as `@[reassoc (attr := simp)])`;
when it is applied to a lemma `foo`, it generates another
lemma `foo_assoc` similarly as `reassoc_of% h` is generated
from `h` above.
:::

# Functors and natural transformations

::: leanSection
```lean -show
variable {C D : Type*} [Category* C] [Category* D]
```

Assuming `C` and `D` are categories, the type `Functor C D`
of functors from `C` to `D` is denoted `C ⥤ D`, where
`⥤` is typed as `\functor`. The identity functor of the
category `C` is `𝟭 C` (where `𝟭` is typed as `\sb1`).
The composition of two functors `F : C₁ ⥤ C₂` and `G : C₂ ⥤ C₃`
is `F ⋙ G : C₁ ⥤ C₃` where `⋙` is typed as `\ggg`. Similarly as
for the composition of morphisms, this composition `F ⋙ G` is
usually denoted `GF` is the mathematical literature.

For example, the identity functor is essentially defined
as follows:
```lean
variable (C) in
-- the actual definition in mathlib is `Functor.id`
@[simps, implicit_reducible]
def Functor.id' : C ⥤ C where
  obj (X : C) := X
  map {X Y : C} (f : X ⟶ Y) := f
```
The action of a functor on objects is `obj`, and its action on morphisms
is `map`. There are two axioms `Functor.map_id` and `Functor.map_comp` in the
`Functor` structure, but they have `by cat_disch` as a default proof.
`cat_disch` is a tactic that is based on `aesop` which closes many
basic goals in category theory (in many cases, `simp` or `ext <;> simp` would
also close goals). In this case, it was able to show that
the identity functor preserves identity morphisms and the composition
of morphisms. Many such goals for other structures in category theory are
also automatically filled by this `cat_disch` tactic.

(The `implicit_reducible` attribute is required for definitions of essentially
all functors. Otherwise, when trying to prove equalities of morphisms involving
the action of functors, Lean may not be able to see through the `obj` fields
of functors. Basically, any definiton of a structure that has a field which
involves objects in a category should be declared `implicit_reducible`.)

The type `C ⥤ D` of functors is endowed with a category structure.
A morphism `f : F ⟶ G` from `F` to `G` in the category of functors `C ⥤ D`
is a natural transformation, i.e. a term in the type `NatTrans F G`.

```lean
#synth Category (C ⥤ D)
variable {F G : C ⥤ D} (f : F ⟶ G)
example (X : C) : F.obj X ⟶ G.obj X := f.app X

/- the naturality of a natural transformation `f : F ⟶ G`
with respect to a morphism `g : X ⟶ Y` in `C` -/
example {X Y : C} (g : X ⟶ Y) :
    F.map g ≫ f.app Y = f.app X ≫ G.map g :=
  f.naturality g
```

Because Lean has a suitable hierarchy of universes, there is no
"set-theoretical" issue regarding the "existence" of functor categories.
Whatever the universe parameters for the categories `C` and `D` are
(and they may be different for `C` and `D`!), the type of functors `C ⥤ D`
and the types of natural transformations `F ⟶ G` between two functors in `C ⥤ D`
live in suitable universes.
:::

# Isomorphisms

::: leanSection
```lean -show
variable {C D : Type*} [Category* C] [Category* D]
```

An isomorphism between two objects `X` and `Y` in a category
`C` is a term `e` in the type `Iso X Y`, which is denoted `X ≅ Y`
(type `≅` as `\cong`). It involves a morphism `e.hom : X ⟶ Y` in
the forward direction, a morphism `e.inv : Y ⟶ X` in the backwards
direction and two axioms `e.hom_inv_id : e.hom ≫ e.inv = 𝟙 X` and
`e.inv_hom_id : e.inv ≫ e.hom = 𝟙 Y` (which Lean tries to auto-fill
`by cat_disch`). For example, the composition of two isomorphisms
is defined as follows:
```lean
variable {X Y Z : C} (e₁ : X ≅ Y) (e₂ : Y ≅ Z)

-- the definition in mathlib is `Iso.trans`,
-- and it is denoted `e₁ ≪≫ e₂`
@[simps]
def Iso.trans' : X ≅ Z where
  hom := e₁.hom ≫ e₂.hom
  inv := e₂.inv ≫ e₁.inv
```

In particular, if `F` and `G` are functors in `C ⥤ D`, we may say that
they are naturally isomorphic when we have `e : F ≅ G`:
```lean
variable {F G : C ⥤ D} (e : F ≅ G)
example (X : C) : F.obj X ≅ G.obj X := e.app X
```

Terms in the type of isomorphisms `X ≅ Y` contain data. We also
have a `Prop`-valued typeclass `IsIso f` which can be used to
express that a morphism `f : X ⟶ Y` is an isomorphism.
```lean
variable (f : X ⟶ Y) [IsIso f]

-- `inv f` is a choice of inverse to `f`
noncomputable example : Y ⟶ X := inv f
example : f ≫ inv f = 𝟙 X := by simp
example : inv f ≫ f = 𝟙 Y := by simp

-- `asIso f` promotes a morphism `f : X ⟶ Y`
-- to an isomorphism `X ≅ Y` when `[IsIso f]` holds
noncomputable example : X ≅ Y := asIso f
```
:::

# The category of types

If `u` is a universe, `Type u` (which is the type of types in the universe `u`)
is a category: we may call it the category of types. In set-theoretical
foundations, this would be called "the category of sets".

If `f : X ⟶ Y` is a morphism in the category of types, one may evaluate
it at `x : X`:
::: leanSection
```lean
example {X Y : Type u} (f : X ⟶ Y) (x : X) : Y := f x
```
:::

If `X` and `Y` are types, the type of morphisms `X ⟶ Y` in the category of types
is not definitionally equal to the type `X → Y` of functions from `X` to `Y`. In order
to define a morphism, we use a constructor that we access using the
notation `↾` (typed as `\uprightharpoon`). The map `x ↦ x ^ 2` from `ℕ` to `ℕ`,
as a morphism in the category of types, can be defined as:
```lean
example : ℕ ⟶ ℕ := ↾(fun x ↦ x ^ 2)
```

# Yoneda's lemma

If `C` is a category (with morphisms in the universe `v`), the Yoneda embedding is
a fully-faithful embedding of `C` in the category of presheaves `Cᵒᵖ ⥤ Type v`. It sends
an object `X : C` to the presheaf `yoneda.obj X` that is represented by `X`:
this is the functor `Cᵒᵖ ⥤ Type v` which sends `Y : C` (considered as an object of `Cᵒᵖ`)
to the type `Y ⟶ X`:
::: leanSection
```lean
variable {C : Type u} [Category.{v} C]

example : C ⥤ Cᵒᵖ ⥤ Type v := yoneda

example {X Y : C} :
    (yoneda.obj X).obj (.op Y) = (Y ⟶ X) := by
  with_implicit rfl

example : (yoneda : C ⥤ _).Faithful := inferInstance
example : (yoneda : C ⥤ _).Full := inferInstance
```

We used the `Prop`-valued typeclasses `Functor.Faithful` and `Functor.Full` in order to
state that `yoneda : C ⥤ Cᵒᵖ ⥤ Type v` is fully faithful, but we also have a structure
`Functor.FullyFaithful` which contains the data of preimages of morphisms by a functor.

```lean
example : (yoneda : C ⥤ _).FullyFaithful where
  preimage {X Y} f := f.app _ (𝟙 X)
  map_preimage {X Y} f := by
    ext _ g
    simpa using congr($(f.naturality g.op) (𝟙 X)).symm
```

More generally, if `F : Cᵒᵖ ⥤ Type v` is a presheaf of types and `X : C`,
there is a bijection between the type of natural transformations `yoneda.obj X ⟶ F`
and the type `F.obj (.op X)` of "sections" of `F` on `X`:
```lean
example {X : C} {F : Cᵒᵖ ⥤ Type v} :
    (yoneda.obj X ⟶ F) ≃ F.obj (.op X) :=
  yonedaEquiv
```

In addition to the `yoneda` bifunctor which is such that the target types are
in `Type v` (which is the universe where morphisms in the category `C` live),
we have a variant `uliftYoneda` which lift the types of morphisms into `Type max v w`,
and the more general variant `shrinkYoneda` which applies to locally `w`-small categories:
```lean
noncomputable example :
    C ⥤ Cᵒᵖ ⥤ Type max v w :=
  uliftYoneda

noncomputable example [LocallySmall.{w} C] :
    C ⥤ Cᵒᵖ ⥤ Type w :=
  shrinkYoneda
```
:::

# Concrete categories

When doing constructions or stating theorems about concrete categories,
a concrete category `C` can be introduced by using the following variables:
::: leanSection
```lean
variable {C : Type*} [Category* C]
  {FC : C → C → Type*} {CC : C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w} C FC]
```
This roughly means that a type `CC X` is attached to any object `X : C`,
that the types of morphisms `X ⟶ Y` in the category `C` can be identified
(up to a bijection) with a type `FC X Y` and that `FC X Y` injects into
the type of functions `CC X → CC Y`.

For example, if `R` is a ring, the category `ModuleCat R` is a concrete category,
with `CC` being the underlying type of a `R`-module and `FC` the type of
linear maps:
```lean
variable (R : Type*) [Ring R]
#synth ConcreteCategory (ModuleCat R) (· →ₗ[R] ·)
```
Note that the types of morphisms in `ModuleCat R` are not defined directly using
types of linear maps (they are defined using a `1`-field structure), but for
the concrete category instance, we use `· →ₗ[R] ·`.

If `C` is a concrete category, we have a faithful forgetful functor to the category
of types:
```lean
example : C ⥤ Type w := forget C
#synth (forget C).Faithful

-- `ToType` is an abbreviation for `CC`,
-- and if `f : X ⟶ Y` and `x : ToType X`,
-- the syntax `f x` allows to evaluate `f` at `x`:
example {X Y : C} (f : X ⟶ Y) (x : ToType X) :
  ToType Y := f x
```

The lemma `comp_apply` relates the composition of morphisms and
the evaluation:
```lean
variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
example : f ≫ g = h ↔ ∀ x, g (f x) = h x := by
  simp only [ConcreteCategory.hom_ext_iff, comp_apply]
```
:::

# Full subcategories

::: leanSection
```lean -show
variable {C : Type*} [Category* C]
```

If `C` is a category, there is a type `ObjectProperty C` of properties
of objects of `C`, i.e. predicates `C → Prop`. For example, if `X` is an
object of a category `C`, one may define the property of objects of `C`
that are isomorphic to `X`, show that this property is closed
under isomorphisms, and that it is the closure under isomorphisms of
the property of objects that is only satisfied by `X`:

```lean
variable (X : C)

def isIsomorphicTo : ObjectProperty C :=
  fun Y ↦ Nonempty (X ≅ Y)

instance :
    (isIsomorphicTo X).IsClosedUnderIsomorphisms where
  of_iso := by
    intro _ _ e₁ ⟨e₂⟩
    exact ⟨e₂ ≪≫ e₁⟩

example :
    isIsomorphicTo X =
      (ObjectProperty.singleton X).isoClosure := by
  refine le_antisymm ?_ ?_
  · intro _ ⟨e⟩
    exact ⟨X, by simp, ⟨e.symm⟩⟩
  · rw [ObjectProperty.isoClosure_le_iff]
    intro _ ⟨_⟩
    exact ⟨Iso.refl _⟩
```

The full subcategory of `C` consisting of objects `X : C` satisfying
a given property `P : ObjectProperty C` is `P.FullSubcategory` and
the inclusion functor `P.FullSubcategory ⥤ C` is `P.ι`:
```lean
#synth Category (isIsomorphicTo X).FullSubcategory

example : (isIsomorphicTo X).FullSubcategory ⥤ C :=
  (isIsomorphicTo X).ι
```

Similarly to the type `ObjectProperty C` of properties of objects of `C`,
we have the type `MorphismProperty C` of properties of morphisms in `C`
(which resembles the type `ObjectProperty (Arrow C)` of properties
of objects in the category of arrows in `C`). Similarly, certain typeclasses
express that `W : MorphismProperty C` is stable under composition
(`MorphismProperty.IsStableUnderComposition`), is stable under
base change (`MorphismProperty.IsStableUnderBaseChange`), etc.
If `W : MorphismProperty C` is multiplicative (`MorphismProperty.IsMultiplicative`),
i.e. contains identities and is stable under composition, then we may also
consider the widesubcategory of `C` consisting of the morphisms satisfying `W`:
```lean
variable (W : MorphismProperty C) [W.IsMultiplicative]
#synth Category (WideSubcategory W)
```
:::

# Equivalences of categories

An equivalence between two categories `C` and `D` is a term in the
type `Equivalence C D`, which is denoted `C ≌ D`, where `≌` (typed as `\backcong`)
should not be confused with `≅` (typed as `\cong`). Such a an equivalence
consists of two functors `functor : C ⥤ D` and `inverse : D ⥤ C`,
and two isomorphisms `unitIso : 𝟭 C ≅ functor ⋙ inverse` and
`counitIso : inverse ⋙ functor ≅ 𝟭 D` which satisfy a triangle identity
(similarly as units and counits of adjunctions do).

The equivalence between the opposite of the opposite of a category `C`
and the category `C` can be defined as follows:
:::leanSection
```lean
-- the mathlib definition is `opOpEquivalence`
@[simps, implicit_reducible]
def opOpEquivalence' (C : Type*) [Category* C] :
    Cᵒᵖᵒᵖ ≌ C where
  functor.obj X := X.unop.unop
  functor.map f := f.unop.unop
  inverse.obj X := .op (.op X)
  inverse.map f := f.op.op
  unitIso := Iso.refl _
  counitIso := Iso.refl _
```
:::

# Limits

Mathlib has a significant API for (co)limits in a category `C`. If `F : J ⥤ C`
is a functor and its limit exists `[HasLimit F]`, we may let Lean choose
such a limit:

:::leanSection
```lean -show
variable {J C : Type*} [Category* J] [Category* C]
```

```lean
variable (F : J ⥤ C) [HasLimit F]

-- a choice of a limit for a functor `F : J ⥤ C`
noncomputable example : C := limit F

noncomputable example (j : J) : limit F ⟶ F.obj j :=
  limit.π F j

-- if `c` is a cone for a functor, this is the canonical
-- morphism from the point of `c` to the limit of `F`
noncomputable example (c : Cone F) : c.pt ⟶ limit F :=
  limit.lift F c
```

The "chosen" limit `limit F` should be used only when we
need to make such a choice. Otherwise, it is recommended
to use cones `c : Cone F` which satisfy the condition
`IsLimit c` (which contains data), which is a way to express
that the point `c.pt` of the cone `c` satisfies the
universal property of the limit of `F`.
:::
