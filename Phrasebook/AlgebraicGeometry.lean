/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Phrasebook.Meta.Lean
import VersoManual

open Phrasebook
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Schemes in Mathlib" =>

This page explains how to express common concepts in scheme theory
using the definitions in Mathlib.
We assume basic knowledge of both Lean and algebraic geometry in the language of schemes.

```lean -show
universe u
```

Most declarations are in the `AlgebraicGeometry` namespace and since we rely
on the language of category theory, we recommend to have the following namespaces open.

```lean
open AlgebraicGeometry CategoryTheory Limits
```

In what follows, most definitions are `noncomputable`. Starting with a `noncomputable`
section is therefore recommended.
```lean
noncomputable section
```

The exposition is split in the following subsections:

# Prime spectrum

::: leanSection
Let `R` and `S` be commutative rings.
```lean
variable {R S : Type} [CommRing R] [CommRing S]
```
The basic building block of algebraic geometry is the prime spectrum of a ring,
which is the type {name}`PrimeSpectrum`.
```lean
#check PrimeSpectrum R
```
To provide a term of type {lean}`PrimeSpectrum R`, we need to provide an ideal of {lean}`R`
with a proof that `p` is a prime ideal.
```lean
example (p : Ideal R) [p.IsPrime] : PrimeSpectrum R :=
  ⟨p, (inferInstance : p.IsPrime)⟩
```
It is endowed with a structure of topological space: the Zariski topology.
```lean
example : TopologicalSpace (PrimeSpectrum R) :=
  inferInstance
```
A ring homomorphism induces a function on prime spectra:
```lean
example (f : R →+* S) : PrimeSpectrum S → PrimeSpectrum R :=
  PrimeSpectrum.comap f
```
We can construct sets in the prime spectrum with the familiar constructions. For example,
this is the set $`\mathrm{V}(s) \cap \mathrm{D}(f)`:
```lean
example (s : Set R) (f : R) : Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus s ∩ PrimeSpectrum.basicOpen f
```
:::

# The unbundled vs. bundled barrier.

When working in algebraic geometry in mathlib, we often have to cross the
_unbundled vs. bundled_ barrier. To explain what we mean by this, consider the following
example:

The composition of two ring homomorphisms can be expressed as:
```lean -show
variable {R S T : Type} [CommRing R] [CommRing S]
```
```lean
example (R S T : Type) [CommRing R] [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T) :
    R →+* T :=
  RingHom.comp g f
```
or as:
```lean
example (R S T : CommRingCat) (f : R ⟶ S) (g : S ⟶ T) :
    R ⟶ T :=
  f ≫ g
```
The first approach is called _unbundled_ and the second one _bundled_: In the first version,
the {lean}`CommRing` structure on `R` is provided as a separate argument. It is unbundled from the
type `R`. In the second version, the `CommRing` structure is bundled with the type in a term
`R` of type {lean}`CommRingCat`.

Note that we have to write {lean}`R →+* S` in the first case to talk about a ring homomorphism `f`. This
is because `R S : Type`. In the case of `R S : CommRingCat`, the types contain enough information
to infer that `R ⟶ S` denotes a ring homomorphism.

Moreover, in the bundled version we can use the notation `f ≫ g` to denote composition of the
ring homomorphisms `f` and `g`.

Most of the topology and commutative algebra library is written in the unbundled style. But
to talk about the _category_ of commutative rings or the _category_ of topological spaces, this
category needs a _type of objects_.
```lean
example : Type 1 := CommRingCat
```
To go between the unbundled and the bundled world, use {name}`CommRingCat.of` and
{name}`CommRingCat.ofHom`. For example:
```lean
example (R S : Type) [CommRing R] [CommRing S]
    (f : R →+* S) :
    CommRingCat.of R ⟶ CommRingCat.of S :=
  CommRingCat.ofHom f
```
Conversely, a morphism in {name}`CommRingCat` has an underlying ring homomorphism.
```lean
example (R S : CommRingCat) (f : R ⟶ S) : R →+* S := f.hom
```
We can still apply a morphism in `CommRingCat` to an element.
```lean
example (R S : CommRingCat) (f : R ⟶ S) (x : R) : S := f x
```
The type of commutative rings is endowed with a category structure.
```lean
open CategoryTheory -- required for category notation
example : Category CommRingCat := inferInstance
```
This allows us to write `𝟙 _` for the identity and `_ ≫ _` for composition:
```lean
example (R S : CommRingCat) (f : R ⟶ S) : R ⟶ S :=
  𝟙 R ≫ f ≫ 𝟙 S
```

# Schemes

::: leanSection
As you would expect, a {name}`Scheme` is defined as a locally ringed space that is locally
isomorphic to the spectrum of a ring.
```lean
#check Scheme
```
```lean -show
variable {R S : CommRingCat}
```
If {lean}`R` is a ring, the prime spectrum of {lean}`R` viewed as a scheme is {lean}`Spec R`
and given a morphism {lean}`R ⟶ S`, the induced morphism of schemes is:
```lean
example (f : R ⟶ S) : Spec S ⟶ Spec R :=
  Spec.map f
```
Note that the underlying type of {lean}`Spec R` is {lean}`PrimeSpectrum R`.
Let now `X`, `Y` and `Z` be schemes.
```lean
variable {X Y Z : Scheme}
```
```lean -show
variable {U V : X.Opens}
```
As before, we can compose morphisms of schemes in the same way as we can compose
morphisms of commutative rings:
```lean
example (f : X ⟶ Y) : X ⟶ Y := f ≫ 𝟙 Y
```
We can apply a morphism of schemes to an element.
```lean
example (f : X ⟶ Y) (x : X) : Y := f x
```
Sections of the structure sheaf $`\mathcal{O} = \mathcal{O}_X` over an open can be written
with the notation `Γ(X, U)`:
```lean
example (U : X.Opens) : CommRingCat :=
  Γ(X, U)
```
If {lean}`U` is contained in {lean}`V`, we get a restriction map $`\mathcal{O}(V) \to \mathcal{O}(U)`:
```lean
example (U V : X.Opens) (hUV : U ≤ V) : Γ(X, V) ⟶ Γ(X, U) :=
  X.presheaf.map (homOfLE hUV).op
```
Given a morphism `f` and an open `V`, we obtain a morphism
$`\mathcal{O}_Y(U) ⟶ \mathcal{O}_X(f^{-1}(U))`.
```lean
example (f : X ⟶ Y) (U : Y.Opens) :
    Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  f.app U
```
A variant we often encounter is the composition
$`\mathcal{O}_Y(U) \to \mathcal{O}_X(f^{-1}(U)) \to \mathcal{O}_X(V)`.
```lean
example (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) : Γ(Y, U) ⟶ Γ(X, V) :=
  f.appLE U V h
```
To restrict a morphism of schemes to an open of the target, we can use:
```lean
example (f : X ⟶ Y) (U : Y.Opens) :
    (f ⁻¹ᵁ U : Scheme) ⟶ U :=
  f ∣_ U
```
One of the reasons we use the bundled approach for {name}`Scheme`s, is the heavy reliance on category
theoretical constructions.

The fibre product of schemes is simply the application of the general {name}`pullback` to the
category of {name}`Scheme`s.
```lean
example (f : X ⟶ Z) (g : Y ⟶ Z) : Scheme :=
  pullback f g
```
To access the projections, use {name}`pullback.fst` and {name}`pullback.snd`.
Note: `f ∣_ U` is _not_ the projection
$`X \times_{Y} U \to U`.

We have already seen the functorial properties of {lean}`Spec` above. Sometimes we
have to interact with {lean}`Spec` as a functor:
```lean
example : CommRingCatᵒᵖ ⥤ Scheme :=
  Scheme.Spec
```
Note the difference between {lean}`Spec` and {lean}`Scheme.Spec`.

In this language, the $`\Gamma`-Spec adjunction is phrased as:
```lean
example : Scheme.Γ.rightOp ⊣ Scheme.Spec :=
  ΓSpec.adjunction
```
:::

# Affine schemes

::: leanSection

```lean -show
variable (X Y Z : Scheme)
```

Among all schemes, the affine schemes take an important role and we use
the predicate {name}`IsAffine` to say a scheme is affine. For example,
`Spec R` is affine:
```lean
example (R : CommRingCat) : IsAffine (Spec R) :=
  inferInstance
```
If {lean}`X` is an affine scheme, it is isomorphic to {lean}`Spec Γ(X, ⊤)`.
```lean
example [IsAffine X] : X ≅ Spec Γ(X, ⊤) :=
  X.isoSpec
```
Some proofs of being affine can be found by instance synthesis.
```lean
example (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsAffine X] [IsAffine Y] [IsAffine Z] :
    IsAffine (pullback f g) :=
  inferInstance
```
:::

# Stalks, residue fields and fibres

::: leanSection
To get acquainted with the scheme API, let us consider an example: Let us define
the fibre of a morphism of schemes.
```lean
variable {X Y : Scheme} (f : X ⟶ Y)
```
The stalk `𝒪_Y,y` of `𝒪_Y` at the point `y`.
```lean
example (y : Y) : CommRingCat := Y.presheaf.stalk y
```
The stalk `𝒪_Y,y` is a local ring.
```lean
#synth ∀ y, IsLocalRing (Y.presheaf.stalk y)
```
And we may consider its residue field.
```lean
example (y : Y) : Type :=
  IsLocalRing.ResidueField (Y.presheaf.stalk y)
```
The morphism `Spec κ(y) ⟶ Y`.
```lean
example (y : Y) : Spec (Y.residueField y) ⟶ Y :=
  Y.fromSpecResidueField y
```
The fibre of `f` over `y` is, by definition, the fibre product
```
X ×[Y] Spec κ(y) ------> Spec κ(y)
      |                       |
      |                       |
      v                       |
      X --------------------> Y
```
```lean
def fiber (y : Y) : Scheme :=
  pullback f (Y.fromSpecResidueField y)
```
The immersion `X ×[Y] Spec κ(y) ⟶ X`:
```lean
def fiberι (y : Y) : fiber f y ⟶ X :=
  pullback.fst f (Y.fromSpecResidueField y)
```
The projection `X ×[Y] Spec κ(y) ⟶ Spec κ(y)`.
```lean
def fiberToSpecResidueField (y : Y) :
    fiber f y ⟶ Spec (Y.residueField y) :=
  pullback.snd f (Y.fromSpecResidueField y)
```
In `Mathlib` these are called {lean}`Scheme.Hom.fiber`, {lean}`Scheme.Hom.fiberι` and
{lean}`Scheme.Hom.fiberToSpecResidueField` and we can
for example write {lean}`f.fiber`.
:::

# Subschemes

`Mathlib` does not have a definition of subschemes, we simply use morphisms `Z ⟶ X`
with the relevant properties. We give two prominent examples of such properties
and how to construct them.

## Open subschemes

::: leanSection
```lean -show
variable {U V X Y : Scheme}
```
Given an open subset of {lean}`X`, we can naturally regard it as a scheme.
```lean
example (U : X.Opens) : Scheme := U
example (U : X.Opens) : (U : Scheme) ⟶ X := U.ι
```
Instead of working with `U : X.Opens`, it is often convenient to allow arbitrary
open immersions instead.
```lean
example (f : U ⟶ X) [IsOpenImmersion f] : X.Opens :=
  f.opensRange
```
We rely on typeclass inference to automatically fill proofs using stability properties.
```lean
example (f : U ⟶ V) (g : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) :=
  inferInstance
```
:::

## Closed subschemes

A closed subscheme is a morphism satisfying {lean}`IsClosedImmersion`. For example,
this proves that the range of a closed immersion is closed:
```lean
example (f : Y ⟶ X) [IsClosedImmersion f] :
    IsClosed (Set.range f) :=
  f.isClosedEmbedding.isClosed_range
```
A closed immersion determines an ideal sheaf.
```lean
example (f : Y ⟶ X) [IsClosedImmersion f] :
    X.IdealSheafData :=
  f.ker
```
And conversely, every ideal sheaf determines a closed immersion.
```lean
example :
    (MorphismProperty.Over @IsClosedImmersion ⊤ X)ᵒᵖ ≌
      X.IdealSheafData :=
  IsClosedImmersion.overEquivIdealSheafData X
```

# Properties of morphisms

We have already seen two properties of morphisms in the previous section. `Mathlib` knows many
properties of morphisms. Browsing the `AlgebraicGeometry/Morphisms` folder
gives an overview. The properties are defined as type classes, so many basic proofs
are automatic by `inferInstance`:
```lean
example (f : X ⟶ Z) (g : Y ⟶ Z) [IsProper f] :
    IsSeparated (pullback.snd f g) :=
  inferInstance
```
To unify the handling of the meta properties of these properties of morphisms,
we rely on {lean}`MorphismProperty`. Any of the properties we have seen before
can be viewed as a {lean}`MorphismProperty` by prepending `@`:
```lean
example : MorphismProperty Scheme :=
  @IsClosedImmersion
```
There exist meta properties for morphism properties, for example
being stable under composition, base change, etc.
```lean
#check MorphismProperty.IsStableUnderComposition
#check MorphismProperty.IsStableUnderBaseChange
#check MorphismProperty.RespectsIso
```
and also some more technical ones:
```lean
#check MorphismProperty.HasOfPostcompProperty
```
Besides properties of properties, we also use abstract constructions of properties.
```lean
#check MorphismProperty.universally
#check MorphismProperty.diagonal
#check topologically
```

# Reduction to the affine case

The most important technique in scheme theory is certainly the reduction to
affine situations and commutative algebra. We first explain a few of the
basic tools for this and then give an example how these can be used
to prove a standard fact.

## (Open) covers

::: leanSection
```lean -show
variable (X Y Z : Scheme) (R : CommRingCat)
```

Any reduction to a local problem starts with an (affine) open cover. These
can be pulled back along morphisms, refined, etc.
```lean
#check Scheme.OpenCover
```
Pullback an open cover along an arbitrary morphism:
```lean
example (f : X ⟶ Y) (𝒰 : Y.OpenCover) : X.OpenCover :=
  𝒰.pullback₁ f
```
Refine every component of an open cover by an open cover:
```lean
example (𝒰 : X.OpenCover) (𝒱 : ∀ i, (𝒰.X i).OpenCover) :
    X.OpenCover :=
  𝒰.bind 𝒱
```
A choice of affine cover of `X`.
```lean
example (X : Scheme) : X.OpenCover :=
  X.affineCover
```
The components of `X.affineCover` are _definitionally equal_ to some {lean}`Spec R` for
some {lean}`R`.
```lean
example (X : Scheme) (i : X.affineCover.I₀) :
    ∃ R, X.affineCover.X i = Spec R :=
  ⟨_, rfl⟩
```
:::

## Example

The goal of this section is to define flat morphisms of schemes and to prove
that a morphism is flat if it is stalkwise flat.

```lean -show
variable (P : MorphismProperty Scheme)

#check IsZariskiLocalAtTarget
#check IsZariskiLocalAtSource

#check IsZariskiLocalAtTarget.iff_of_openCover
#check IsZariskiLocalAtSource.iff_of_openCover
```

```lean -show
namespace Example
variable {X Y : Scheme.{u}}
```

Here is a definition of a flat morphism of schemes: A morphism of schemes $`f : X \to Y`
is _flat_ if for every affine open $`U \subseteq Y` and $`V \subseteq f^{-1}(U)`, the
induced ring homomorphism $`\mathcal{O}_Y(U) \to \mathcal{O}_X(V)` is flat.
```lean
@[mk_iff]
class Flat (f : X ⟶ Y) : Prop where
  flat_of_isAffineOpen :
    ∀ (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U),
      IsAffineOpen U → IsAffineOpen V →
      (f.appLE U V e).hom.Flat
```
To connect flat morphisms of schemes to ring homomorphism, we need to provide
an instance of {lean}`HasRingHomProperty`:
```lean
instance :
    HasRingHomProperty @Flat RingHom.Flat where
  isLocal_ringHomProperty := RingHom.Flat.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [flat_iff, affineLocally_iff_affineOpens_le]
    simp only [Scheme.affineOpens, Set.coe_setOf,
      Set.mem_setOf_eq, Subtype.forall]
    grind
```
After this, we get some meta properties for free, for example that flat is local
on the target:
```lean
example : IsZariskiLocalAtTarget @Flat :=
  inferInstance
```

With these preparations, we can now prove that a morphism that is stalkwise flat is flat:
```lean -show
set_option backward.isDefEq.respectTransparency false
```
```lean
theorem flat_of_flat_stalkMap (f : X ⟶ Y)
    (H : ∀ x, (f.stalkMap x).hom.Flat) :
    Flat f := by
  -- We may assume `Y` is of the form `Spec R`
  wlog hY : ∃ R, Y = Spec R generalizing X Y f
  · rw [IsZariskiLocalAtTarget.iff_of_openCover
      (P := @Flat) Y.affineCover]
    intro i
    refine this _ ?_ ⟨_, rfl⟩
    intro x
    rw [RingHom.Flat.respectsIso.arrow_mk_iso_iff]
    · apply H
      dsimp at x
      exact pullback.fst f _ x
    · dsimp [Scheme.Cover.pullbackHom]
      apply Iso.symm <| Scheme.stalkMapIsoOfIsPullback
        (IsPullback.of_hasPullback _ (Y.affineCover.f i)) _
  -- Replace `Y` by `Spec R` in the context and goal.
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X f
  · rw [IsZariskiLocalAtSource.iff_of_openCover
      (P := @Flat) X.affineCover]
    intro i
    refine this _ ?_ ⟨_, rfl⟩
    intro x
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_right_isIso]
    apply H
  -- Replace `X` by `Spec S` in the context and goal.
  obtain ⟨S, rfl⟩ := hX
  -- Replace `f` by `Spec.map φ` in the context and goal.
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  /- Since we have shown before that flat morphisms of
  schemes correspond to flat ring homomorphisms, we can now
  turn the goal into commutative algebra. -/
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  /- Finally, use the fact from commutative algebra, that
  flatness of ring maps can be checked on stalks. -/
  apply RingHom.Flat.ofLocalizationPrime
  intro P hP
  specialize H ⟨P, hP⟩
  rwa [RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso φ _)] at H
```

# More topics

Here are a few more pointers to relevant objects in algebraic geometry, that we
don't explain in detail here.

There is no `AlgebraicGeometry.Variety` and there will most likely never be such a definition.
But you are free to create your local definition of variety (downstream of mathlib),
for example like so:
```lean
class Variety {X : Scheme} {k : Type} [Field k]
      (s : X ⟶ Spec (.of k)) : Prop
    extends IsSeparated s, LocallyOfFiniteType s
```
Function field of a scheme.
```lean
#check Scheme.functionField
```
(Locally) Noetherian schemes.
```lean
#check IsLocallyNoetherian
#check IsNoetherian
```
Projective spectrum of a graded ring.
```lean
variable {σ : Type} {A : Type}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
#check Proj 𝒜
```
