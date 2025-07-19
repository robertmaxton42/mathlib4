/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/

import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.Data.Finite.Defs

/-! # Classes of (co)cones of a given shape

  We extend the definitions of many properties of morphisms to (co)cones of morphisms. Using these,
  we can define a stronger factorisation system for certain categories, that impose the existence of
  factorisations for (co)cones of a given shape as well as individual morphisms.

  This file is adapted from (Shulman, 2012).


  ## Main definitions
  * `HasRestrictedLiftingProperty`
  * `MonoSpan`, its duals, and its refinements
    * A `MonoSpan` is a cone of morphisms `G : (i : ι) → Y ⟶ Z i` that is jointly mono, in that
      for any composable `f, g`, `∀ i, f ≫ G i = g ≫ G i ↔ f = g`.
    * A `StrongMonoSpan` is a mono span `G : (i : ι) → Y₁ ⟶ Z i` which has the right lifting
      property with respect to finite epi cospans when the lifting square is restricted to precisely
      spans and cospans.
    * An `EffectiveMonoSpan` is a cone `G : (i : ι) → Y₁ ⟶ Z i` s.t., for any other cone
      `Q : (i : ι) → Y₂ ⟶ Z i`, if we have some `i j : ι`, `f : Z i ⟶ W`, `g : Z j ⟶ W` s.t.
      `f ≫ G i = g ≫ G j → f ≫ Q i = g ≫ Q j` then there exists a unique `h : Y₂ ⟶ Y₁` s.t.
      `∀ i, h ≫ G i = Q i`.
  * `CospanMonoFactorisation`: a factorisation of cospans `F = E ≫ m`, where `m` is a single mono
    and `E` is a family.
    * `CospanImageFactorisation`: an initial `CospanMonoFactorisation`
    * `StrongEpiCospanMonoFactorisation`: a `CospanMonoFactorisation` where `E` is a
      `StrongEpiCospan`
  * `HasCospanImage`: the mere existence of an `CospanImageFactorisation` instance, and its
    associated API
    * `HasCospanImagesOfShape`: the mere existence of an `CospanImageFactorisation` instance for
      all cospans of a given shape.
    * `HasStrongEpiCospanFactorisationsOfShape`: the mere existence of an
      `StrongEpiCospanMonoFactorisation` instance for all cospans of a given shape.
    * `HasStrongEpiCospanImagesOfShape`: the `CospanImageFactorisation` instance that exists for
      all cospans of a given shape is a `StrongEpiCospanMonoFactorisation`

  We provide duals for `MonoSpan` and `StrongMonoSpan`; the dual to `EffectiveMonoSpan` is
  already implemented in `Mathlib.CategoryTheory.EffectiveEpi.Basic`.

  ## Implementation notes
  `MonoFamily` and `EpiFamily` could have been defined as simply being mono or epi in the
  category of families of objects of `C`, but the other classes cannot: their universal properties
  only apply to what Shulman (2012) calls "arrays", families of morphisms between families of
  objects with exactly one morphism between each pair of objects. Such morphisms do not form a
  category as they are not closed under composition, so e.g. a `StrongEpiFamily` is not
  necessarily `StrongEpi` in `Family C`. For the sake of uniformity, we define `MonoFamily` and
  `EpiFamily` in the same explicit fashion as the others.

  We could also have defined the category `Family C` anyway, and then defined "restricted lifting
  properties" and "restricted (co)limits" that only quantify over the span of some
  `MorphismProperty` (in this case being an array); but as we will not be able to reuse any
  existing API, it is not clear that this would be an improvement.

  ## References
  * [Shulman, 2012](http://www.tac.mta.ca/tac/volumes/27/7/27-07abs.html)
 -/

namespace PUnit
universe w
instance : Finite PUnit.{w + 1} :=
  ⟨{ toFun _ := (0 : Fin 1), invFun _ := ⟨⟩, left_inv _ := by simp, right_inv _ := by aesop }⟩

end PUnit

namespace CategoryTheory
universe w v u
variable {C : Type u} [Category.{v} C]

section cospan_lifting
variable {ι κ : Type w} {A : (i : ι) → C} {B X : C} {Y : (k : κ) → C}


namespace CommSq
variable {F : (i : ι) → A i ⟶ X} {I : (i : ι) → A i ⟶ B}
         {P : (k : κ) → X ⟶ Y k} {G : (k : κ) → B ⟶ Y k}

/-- The datum for a *common* lift of a family of squares made up of opposing (co)spans: given that
```
 A i --F i-→ X
 |           |
I i         P k
 ↓           ↓
 B ---G k-→ Y k
```
commutes for all `i : ι` and `k : κ`, then the datum of a single morphism `B ⟶ Z` that makes both
triangles commute for all `i` and `k`. -/
structure CommonLiftStruct (sq : ∀ i k, CommSq (F i) (I i) (P k) (G k)) where
  /-- The common lift. -/
  l : B ⟶ X
  /-- The upper left triangle commutes for all `i`. -/
  fac_left : ∀ i, I i ≫ l = F i := by aesop_cat
  /-- The lower right triangle commutes for all `k`. -/
  fac_right : ∀ k, l ≫ P k = G k := by aesop_cat

namespace CommonLiftStruct
attribute [reassoc (attr := simp)] fac_left fac_right
variable {sq : ∀ i k, CommSq (F i) (I i) (P k) (G k)}

@[simps]
def toLiftStruct (l : CommonLiftStruct sq) (i k) : LiftStruct (sq i k) where
  l := l.l

instance : CoeFun (CommonLiftStruct sq) (fun _ ↦ (i k : _) → LiftStruct (sq i k)) := ⟨toLiftStruct⟩

end CommonLiftStruct

/-- The mere existence of a common lift for a family of squares. -/
class HasCommonLift (sq : ∀ i k, CommSq (F i) (I i) (P k) (G k)) : Prop where
mk'::
  /-- The common lift struct. -/
  exists_common_lift : Nonempty (CommonLiftStruct sq)

variable {sq : ∀ i k, CommSq (F i) (I i) (P k) (G k)}

def HasCommonLift.mk (l : B ⟶ X) (fac_left : ∀ i, I i ≫ l = F i)
    (fac_right : ∀ k, l ≫ P k = G k) : HasCommonLift sq := ⟨⟨l, fac_left, fac_right⟩⟩

instance [HasCommonLift sq] i k : HasLift (sq i k) where
  exists_lift := ⟨‹HasCommonLift sq›.exists_common_lift.some i k⟩

noncomputable def cLift (sq : ∀ i k, CommSq (F i) (I i) (P k) (G k)) [HasCommonLift sq] : B ⟶ X :=
  ‹HasCommonLift sq›.exists_common_lift.some.l

variable {sq : ∀ i k, CommSq (F i) (I i) (P k) (G k)} [HasCommonLift sq]

@[reassoc (attr := simp)]
lemma comp_cLift i : I i ≫ cLift sq = F i := by simp [cLift]

@[reassoc (attr := simp)]
lemma cLift_comp k : cLift sq ≫ P k = G k := by simp [cLift]

end CommSq
end cospan_lifting

open CommSq

section props
variable {ι κ : Type w}

/-- A cospan `I` indexed by `ι` has the left lifting property with respect to a span `P` indexed by
`κ`, or equivalently a span `P` has the right lifting property with respect to `I`, if for
any cospan `F` indexed by `κ` and span `G` indexed by `ι`, if the square
```
 A i --F i-→ X
 |           |
I i         P k
 ↓           ↓
 B ---G k-→ Y k
```
commutes for all `i : ι` and `k : κ`, then there exists a single morphism `B ⟶ Z` that makes both
triangles commute. -/
class HasCommonLiftingProperty {ι κ : Type w} {A : (i : ι) → C} {B X : C} {Y : (k : κ) → C}
    (I : (i : ι) → A i ⟶ B) (P : (k : κ) → X ⟶ Y k) : Prop where
  sq_hasCommonLift {F : (i : ι) → A i ⟶ X} {G : (k : κ) → B ⟶ Y k}
    (sq : ∀ i k, CommSq (F i) (I i) (P k) (G k)) : HasCommonLift sq

/-- A span -- a family of objects with shared source -- is mono precisely if it is mono in the
category of families of objects of `C`. -/
class MonoSpan {X : C} {Y : ι → C} (F : (i : ι) → X ⟶ Y i) : Prop where
  right_cancellation : ∀ {Z} {g₁ g₂ : Z ⟶ X}, (∀ i, g₁ ≫ F i = g₂ ≫ F i) → g₁ = g₂

instance monoSpan_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : MonoSpan (fun (_ : PUnit) ↦ f) :=
  ⟨fun {_ _ _} h ↦ Mono.right_cancellation _ _ <| h ⟨⟩⟩

instance monoSpan_of_comp_mono {X Y : C} {Z : ι → C} (f : X ⟶ Y) [Mono f]
  (G : (i : ι) → Y ⟶ Z i) [MonoSpan G] : MonoSpan (f ≫ G ·) where
  right_cancellation {Z f₁ f₂} hF := by
    simp_rw [← Category.assoc] at hF
    exact Mono.right_cancellation _ _ <| MonoSpan.right_cancellation hF

/-- A cospan -- a family of objects with shared target -- is epi precisely if it is epi in the
category of families of objects of `C`. -/
class EpiCospan {X : ι → C} {Y : C} (F : (i : ι) → X i ⟶ Y) : Prop where
  left_cancellation : ∀ {Z} {g₁ g₂ : Y ⟶ Z}, (∀ i, F i ≫ g₁ = F i ≫ g₂) → g₁ = g₂

instance epiCospan_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : EpiCospan (fun (_ : PUnit) ↦ f) :=
  ⟨fun {_ _ _} h ↦ Epi.left_cancellation _ _ <| h ⟨⟩⟩

instance epiCospan_of_comp_epi {X : ι → C} {Y Z : C} (F : (i : ι) → X i ⟶ Y) [EpiCospan F]
  (g : Y ⟶ Z) [Epi g] : EpiCospan (F · ≫ g) where
  left_cancellation {Z f₁ f₂} hF := by
    simp_rw [Category.assoc] at hF
    exact Epi.left_cancellation _ _ <| EpiCospan.left_cancellation hF


/-- A span is strongly mono if it is mono and has the right lifting property with respect to epi
cospans when the lifting square is restricted to precisely spans and cospans.

More explicitly, given a square
```
 A k --G k-→ X
 |           |
Q k         F i
 ↓           ↓
 B ---P i-→ Y i
```
with `G` and `Q` finite cospans, `Q` additionally epi, and `P` any span, if the square commutes
for all `i : ι` and `k : κ`, then there exists a single common lift `B ⟶ X` that makes
both triangles commute for all `i` and `k`. -/
class StrongMonoSpan {X : C} {Y : ι → C} (F : (i : ι) → X ⟶ Y i) extends MonoSpan F where
  [rlp {κ : Type w} [Finite κ] ⦃A : κ → C⦄ ⦃B : C⦄ (Q : (k : κ) → A k ⟶ B) [EpiCospan Q] :
    HasCommonLiftingProperty Q F]

namespace StrongMonoSpan
variable {X : C} {Y : ι → C} {κ : Type w} [Finite κ] {A : κ → C} {B : C}
    (Q : (k : κ) → A k ⟶ B) (F : (i : ι) → X ⟶ Y i) [hF : StrongMonoSpan F]
    [EpiCospan Q] {G : (k : κ) → A k ⟶ X} {P : (i : ι) → B ⟶ Y i}
    (sq : ∀ k i, CommSq (G k) (Q k) (F i) (P i))

instance (priority := 100) monoSpan_of_strongMonoSpan : MonoSpan F := hF.toMonoSpan

noncomputable def cLift : B ⟶ X :=
  have := hF.rlp Q |>.sq_hasCommonLift sq
  CommSq.cLift sq

variable {Q F sq} in
@[reassoc (attr := simp)]
lemma cLift_comp i : cLift Q F sq ≫ F i = P i := by simp [cLift]

variable {Q F sq} in
@[reassoc (attr := simp)]
lemma comp_cLift k : Q k ≫ cLift Q F sq = G k := by simp [cLift]

/-- Strong mono families are extremal: if they (collectively) factor through an epi, that epi must
be an isomorphism. -/
def isIso_of_fac_epi {Z : C} (e : X ⟶ Z) [Epi e] {G : (i : ι) → Z ⟶ Y i}
    (fac : ∀ i, e ≫ G i = F i) : IsIso e := by
  constructor
  replace fac : ∀ (k : PUnit) i, (fun _ ↦ 𝟙 X) i ≫ F i = (fun _ ↦ e) k ≫ G i := by
    intro ⟨⟩ k; simp [fac]
  refine ⟨cLift _ F (⟨fac · ·⟩), ?_, ?_⟩
  · rw [comp_cLift (Q := fun _ ↦ e) ⟨⟩]
  · apply Epi.left_cancellation (f := e) _ _
    rw [comp_cLift_assoc (Q := fun _ ↦ e) ⟨⟩]
    simp

/-- Strong mono families respect isomorphisms. -/
instance of_comp_iso {Z : C} (e : Z ⟶ X) [IsIso e] : StrongMonoSpan (e ≫ F ·) where
  rlp {κ} [_] ⦃A B Q⦄ [_] := by
    fapply HasCommonLiftingProperty.mk
    intro P G sq
    fapply HasCommonLift.mk
    · have sq i k : CommSq (P i ≫ e) (Q i) (F k) (G k) := by
        constructor; simp [sq i k |>.w]
      exact cLift Q F sq ≫ inv e
    · intro i; simp
    · intro k; simp

end StrongMonoSpan

/-- A cospan is strongly epi if it is epi and has the left lifting property with respect to mono
spans when the lifting square is restricted to precisely spans and cospans.

More explicitly, given a square
```
 A i --P i-→ X
 |           |
F i         Q k
 ↓           ↓
 B ---G k-→ Y k
```
with `G` and `Q` finite spans, `Q` additionally mono, and `P` any cospan, if the square commutes
for all `i : ι` and `k : κ`, then there exists a single common lift `B ⟶ Y` that makes
both triangles commute for all `i` and `k`. -/
class StrongEpiCospan {A : ι → C} {B : C} (F : (i : ι) → A i ⟶ B) extends EpiCospan F where
  llp {κ : Type w} [Finite κ] ⦃Y : κ → C⦄ ⦃X : C⦄ (Q : (k : κ) → X ⟶ Y k) [MonoSpan Q] :
    HasCommonLiftingProperty F Q := by infer_instance

#check StrongEpiCospan.mk

namespace StrongEpiCospan
variable {A : ι → C} {B : C} (F : (i : ι) → A i ⟶ B) [hF : StrongEpiCospan F]

instance (priority := 100) epiCospan_of_strongEpiCospan : EpiCospan F := hF.toEpiCospan

variable {κ : Type w} [Finite κ] {Y : κ → C} {X : C} (Q : (k : κ) → X ⟶ Y k)
    [MonoSpan Q] {G : (k : κ) → B ⟶ Y k} {P : (i : ι) → A i ⟶ X}
    (sq : ∀ i k, CommSq (P i) (F i) (Q k) (G k))

noncomputable def cLift : B ⟶ X :=
  have := hF.llp Q |>.sq_hasCommonLift sq
  CommSq.cLift sq

variable {F Q sq} in
@[reassoc (attr := simp)]
lemma cLift_comp k : cLift F Q sq ≫ Q k = G k := by simp [cLift]

variable {F Q sq} in
@[reassoc (attr := simp)]
lemma comp_cLift i : F i ≫ cLift F Q sq = P i := by simp [cLift]

/-- Strong epi families are extremal: if they (collectively) factor through a mono, that mono must
be an isomorphism. -/
def isIso_of_fac_mono {Z : C} (m : Z ⟶ B) [Mono m] {G : (i : ι) → A i ⟶ Z}
    (fac : ∀ i, G i ≫ m = F i) : IsIso m := by
  constructor
  replace fac : ∀ i (k : PUnit), G i ≫ (fun _ ↦ m) k = F i ≫ (fun _ ↦ 𝟙 B) k := by
    intro i ⟨⟩; simp [fac]
  refine ⟨cLift F _ (⟨fac · ·⟩), ?_, ?_⟩
  · apply Mono.right_cancellation (f := m) _ _
    rw [Category.assoc, cLift_comp (Q := fun _ ↦ m) ⟨⟩]
    simp
  · rw [cLift_comp (Q := fun _ ↦ m) ⟨⟩]

/-- Strong epi families respect isomorphisms. -/
instance of_comp_iso {Z : C} (e : B ⟶ Z) [IsIso e] : StrongEpiCospan (F · ≫ e) where
  llp {κ} [_] ⦃Y X Q⦄ [_] := by
    fapply HasCommonLiftingProperty.mk
    intro P G sq
    fapply HasCommonLift.mk
    · have sq i k : CommSq (P i) (F i) (Q k) (e ≫ G k) := by
        constructor
        simp [sq i k |>.w]
      exact inv e ≫ cLift F Q sq
    · intro i; simp
    · intro k; simp

end StrongEpiCospan

end props

namespace Limits
variable {α : Type w}
variable {X : α → C} {Y : C} (F : (i : α) → X i ⟶ Y)

/-- A factorisation of a cospan `F = E ≫ m` with `m` mono. -/
structure CospanMonoFactorisation where
  /-- The image object. -/
  I : C
  /-- The inclusion of the image object into the target. -/
  m : I ⟶ Y
  /-- The inclusion is mono. -/
  m_mono : Mono m := by infer_instance
  /-- The factored cospan. -/
  E : (i : α) → X i ⟶ I
  /-- The original cospan factors through the image. -/
  fac : ∀ i, E i ≫ m = F i := by aesop_cat

attribute [reassoc (attr := simp)] CospanMonoFactorisation.fac
attribute [instance] CospanMonoFactorisation.m_mono

variable {F} in
@[ext (iff := false)]
lemma CospanMonoFactorisation.ext
    (fac₁ fac₂ : CospanMonoFactorisation F) (hI : fac₁.I = fac₂.I)
    (hm : fac₁.m = eqToHom hI ≫ fac₂.m) : fac₁ = fac₂ := by
  cases fac₁; cases fac₂; cases hI
  simp only [eqToHom_refl, Category.id_comp] at hm; cases hm
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext i
  apply ‹Mono _›.right_cancellation _ _
  simp_all

namespace CospanMonoFactorisation

@[simps]
noncomputable def ofSingleton {X Y : C} {f : X ⟶ Y} (fac : MonoFactorisation f) :
    CospanMonoFactorisation (fun (_ : PUnit) ↦ f) where
  I := _
  m := fac.m
  E _ := fac.e

@[simps]
noncomputable def toSingleton {X Y : C} {f : X ⟶ Y}
    (fac : CospanMonoFactorisation (fun (_ : PUnit) ↦ f)) : MonoFactorisation f where
  I := _
  m := fac.m
  e := fac.E ⟨⟩

variable {F}
open Function


/-- Simultaneously extend a cospan to a larger shape along an embedding in the index type, while
extending a given cospan mono factorisation with it. Works essentially as `Function.extend`: values
in the range of `f` are taken from the original factorisation, and values outside the range are sent
to a junk value (`Nonempty.some`).

This is mostly useful in the reverse direction, using factorisations of large cospans to construct
factorisations of smaller cospans. -/
@[simps]
noncomputable def extend [Nonempty α] (fac : CospanMonoFactorisation F) {β : Type w} (f : α ↪ β) :
    CospanMonoFactorisation (F <| invFun f ·) where
  I := fac.I
  m := fac.m
  E j := fac.E (invFun f j)



/-- Re-restrict an `extend`ed cospan mono factorisation. -/
@[simps]
noncomputable def restrict [Nonempty α] {β : Type w} (f : α ↪ β)
    (fac : CospanMonoFactorisation (F <| invFun f ·)) :
    CospanMonoFactorisation F where
  I := fac.I
  m := fac.m
  E i := eqToHom (by simp [Function.leftInverse_invFun f.injective i]) ≫ fac.E (f i)
  fac i := by simp [← eqToHom_naturality (g := fun _ ↦ Y) F
    (Function.leftInverse_invFun f.injective i).symm]


end CospanMonoFactorisation

variable {F}

/-- A witness that a given cospan mono factorisation is initial. -/
structure IsCospanImage (fac : CospanMonoFactorisation F) where
  /-- Given any other `CospanMonoFactorisation F`, an arrow between the images. -/
  lift (fac' : CospanMonoFactorisation F) : fac.I ⟶ fac'.I
  /-- The lift commutes with the factorisations. -/
  lift_fac (fac' : CospanMonoFactorisation F) : lift fac' ≫ fac'.m = fac.m

attribute [reassoc (attr := simp)] IsCospanImage.lift_fac

/-- The image is unique up to isomorphism. -/
def IsCospanImage.ext {fac₁ fac₂ : CospanMonoFactorisation F}
    (h₁ : IsCospanImage fac₁) (h₂ : IsCospanImage fac₂) : fac₁.I ≅ fac₂.I where
  hom := h₁.lift fac₂
  inv := h₂.lift fac₁
  hom_inv_id := by
    apply fac₁.m_mono.right_cancellation _ _
    simp [h₁.lift_fac fac₂]
  inv_hom_id := by
    apply fac₂.m_mono.right_cancellation _ _
    simp [h₂.lift_fac fac₁]

instance {fac₁ fac₂ : CospanMonoFactorisation F}
    (h₁ : IsCospanImage fac₁) (h₂ : IsCospanImage fac₂) : IsIso (h₁.lift fac₂) :=
  Iso.isIso_hom (h₁.ext h₂)

namespace IsCospanImage

@[simps]
noncomputable def ofSingleton {X Y : C} {f : X ⟶ Y} {fac : MonoFactorisation f}
    (im : IsImage fac) : IsCospanImage (CospanMonoFactorisation.ofSingleton fac) where
  lift fac' := im.lift (CospanMonoFactorisation.toSingleton fac')
  lift_fac fac' := im.lift_fac (CospanMonoFactorisation.toSingleton fac')

@[simps]
noncomputable def toSingleton {X Y : C} {f : X ⟶ Y}
    {fac : CospanMonoFactorisation (fun (_ : PUnit) ↦ f)} (im : IsCospanImage fac) :
    IsImage (CospanMonoFactorisation.toSingleton fac) where
  lift fac' := im.lift (CospanMonoFactorisation.ofSingleton fac')
  lift_fac fac' := im.lift_fac (CospanMonoFactorisation.ofSingleton fac')

/-- An extended cospan mono factorisation is still an image factorisation if the original was. -/
@[simps]
noncomputable def extend [Nonempty α] {β : Type w} {fac : CospanMonoFactorisation F}
    (im : IsCospanImage fac) (f : α ↪ β) : IsCospanImage (fac.extend f) where
  lift fac' := im.lift (fac'.restrict f)
  lift_fac fac' := im.lift_fac (fac'.restrict f)

open Function in
/-- A restricted cospan mono factorisation is still an image factorisation if the original was. -/
@[simps]
noncomputable def restrict [Nonempty α] {β : Type w} (f : α ↪ β)
    {fac : CospanMonoFactorisation (F <| invFun f ·)} (im : IsCospanImage fac) :
    IsCospanImage (fac.restrict f) where
  lift fac' := im.lift (fac'.extend f)
  lift_fac fac' := im.lift_fac (fac'.extend f)

end IsCospanImage

@[simp]
lemma IsCospanImage.lift_self {fac : CospanMonoFactorisation F} (h : IsCospanImage fac) :
    h.lift fac = 𝟙 _ := by
  apply fac.m_mono.right_cancellation _ _
  simp [h.lift_fac fac]

variable (F) in
structure CospanImageFactorisation where
  fac : CospanMonoFactorisation F
  isCospanImage : IsCospanImage fac

-- namespace CospanImageFactorisation
-- open Set Function


-- def ofEmpty [h₀ : IsEmpty α] : CospanImageFactorisation F where
--   fac := { I := Y, m := 𝟙 Y, E := h₀.elim, fac := h₀.elim }
--   isCospanImage := by
--     fconstructor
--     · rintro ⟨I, m, _, _, _⟩
--       simp

-- end CospanImageFactorisation

variable (F) in
class HasCospanImage : Prop where
mk'::
  exists_cospanImage : Nonempty (CospanImageFactorisation F)

def HasCospanImage.mk (fac : CospanImageFactorisation F) : HasCospanImage F := ⟨⟨fac⟩⟩

variable [HasCospanImage F]
variable (F)

/-- Some cospan image factorisation (selected with choice). -/
noncomputable def cImage.cospanMonoFactorisation : CospanMonoFactorisation F :=
  (HasCospanImage.exists_cospanImage (F := F)).some.fac

/-- Some witness that `cospanMonoFactorisation` is initial. -/
noncomputable def cImage.isCospanImage : IsCospanImage (cImage.cospanMonoFactorisation F) :=
  (HasCospanImage.exists_cospanImage (F := F)).some.isCospanImage

/-- The categorical image of a cospan. -/
noncomputable def cImage : C := cImage.cospanMonoFactorisation F |>.I

/-- The inclusion of the categorical image into the target. -/
noncomputable def cImage.ι : cImage F ⟶ Y := cImage.cospanMonoFactorisation F |>.m

@[simp]
lemma cImage.as_ι : (cImage.cospanMonoFactorisation F).m = cImage.ι F := rfl

/-- The inclusion of the categorical image into the target is mono. -/
instance : Mono (cImage.ι F) := cImage.cospanMonoFactorisation F |>.m_mono

/-- The factored cospan. -/
noncomputable def factorThruCImage (i : α) : X i ⟶ cImage F :=
  cImage.cospanMonoFactorisation F |>.E i

@[simp]
lemma as_factorThruCImage (i : α) : (cImage.cospanMonoFactorisation F).E i = factorThruCImage F i :=
  rfl

@[reassoc (attr := simp)]
lemma cImage.fac (i : α) : factorThruCImage F i ≫ cImage.ι F = F i :=
  cImage.cospanMonoFactorisation F |>.fac i

variable {F}

/-- Any other factorisation of `F` through a mono receives a lift from the image. -/
noncomputable def cImage.lift (fac' : CospanMonoFactorisation F) : cImage F ⟶ fac'.I :=
  cImage.isCospanImage F |>.lift fac'

@[simp]
lemma cImage.as_lift (fac' : CospanMonoFactorisation F) :
    (cImage.isCospanImage F).lift fac' = cImage.lift fac' := rfl

/-- Any other image factorisation of `F` has categorical image isomorphic to `cImage F`. -/
@[simps!]
noncomputable def cImage.ext {fac' : CospanMonoFactorisation F} (h : IsCospanImage fac') :
    fac'.I ≅ cImage F :=
  h.ext <| cImage.isCospanImage F

instance {fac' : CospanMonoFactorisation F} (h : IsCospanImage fac') :
    IsIso (cImage.lift fac') := inferInstanceAs (IsIso (cImage.ext h).inv)

@[simp]
lemma cImage.lift_self : cImage.lift (cImage.cospanMonoFactorisation F) = 𝟙 _ := by
  unfold lift; simp [cImage]

@[reassoc (attr := simp)]
lemma cImage.lift_fac (fac' : CospanMonoFactorisation F) :
    cImage.lift fac' ≫ fac'.m = cImage.ι F :=
  cImage.isCospanImage F |>.lift_fac fac'

instance cImage.lift_mono (fac' : CospanMonoFactorisation F) : Mono (cImage.lift fac') := by
  convert mono_of_mono (cImage.lift fac') fac'.m
  rw [cImage.lift_fac]; infer_instance

/-- Lifts are unique. -/
lemma HasCospanImage.uniq (fac' : CospanMonoFactorisation F) (l : cImage F ⟶ fac'.I)
    (w : l ≫ fac'.m = cImage.ι F) : l = cImage.lift fac' := by
  apply fac'.m_mono.right_cancellation _ _
  rwa [cImage.lift_fac fac']

@[ext (iff := false)]
lemma cImage.hom_ext {Z : C} {g₁ g₂ : cImage F ⟶ Z} [HasEqualizer g₁ g₂]
    (w : ∀ i, factorThruCImage F i ≫ g₁ = factorThruCImage F i ≫ g₂) : g₁ = g₂ := by
  let E' (i : α) := equalizer.lift _ (w i)
  let fac' : CospanMonoFactorisation F := { I := _, m := equalizer.ι g₁ g₂ ≫ cImage.ι F, E := E' }
  let im' : IsCospanImage fac' :=
    { lift fac'' := equalizer.ι g₁ g₂ ≫ cImage.lift fac''
      lift_fac fac'' := by simp [fac'] }
  let ε := cImage.ext im'
  have : cImage.lift fac' ≫ equalizer.ι g₁ g₂ = 𝟙 _ := by
    convert ε.inv_hom_id; simp [ε, im']
  fapply Epi.left_cancellation (f := 𝟙 _)
  simp [← this, equalizer.condition]

instance [∀ {Z} {g₁ g₂ : cImage F ⟶ Z}, HasEqualizer g₁ g₂] :
    EpiCospan (factorThruCImage F) where
  left_cancellation {_} _ _ hg := cImage.hom_ext hg


namespace HasCospanImage

/-- If we have a normal image for a cospan, then we have a cospan image for its singleton cospan. -/
instance ofSingleton {X Y : C} (f : X ⟶ Y) [HasImage f] :
    HasCospanImage (fun (_ : PUnit) ↦ f) where
  exists_cospanImage := ⟨⟨
  { I := _
    m := image.ι f
    m_mono := inferInstance
    E _ := factorThruImage f},
  { lift fac := image.lift (CospanMonoFactorisation.toSingleton fac)
    lift_fac fac := image.lift_fac (CospanMonoFactorisation.toSingleton fac) }⟩⟩

/-- If we have a cospan image for a singleton cospan, then we have a normal image for its single
morphism. -/
instance toSingleton {X Y : C} {f : X ⟶ Y} [HasCospanImage (fun (_ : PUnit) ↦ f)] :
    HasImage f where
  exists_image := ⟨⟨
  { I := _
    m := cImage.ι (fun (_ : PUnit) ↦ f)
    e := factorThruCImage (fun (_ : PUnit) ↦ f) ⟨⟩ },
  { lift fac := cImage.lift (CospanMonoFactorisation.ofSingleton fac)
    lift_fac fac := cImage.lift_fac (CospanMonoFactorisation.ofSingleton fac) }⟩⟩

section extendIso

open Function
variable {I J : Type w} [Nonempty I] {X : I → C} {Y : C} (F : (i : I) → X i ⟶ Y) (f : I ↪ J)
         [HasCospanImage F] [HasCospanImage (F <| invFun f ·)]

/-- The image of a cospan produced via `extend` is isomorphic to the image of the original cospan.
-/
noncomputable def extendIso : cImage (F <| invFun f ·) ≅ cImage F :=
  (cImage.ext <| (cImage.isCospanImage F).extend f).symm

@[reassoc (attr := simp)]
lemma factorThruCImage_extendIso_hom_mem (i : I) :
    factorThruCImage (F <| invFun f ·) (f i) ≫ (extendIso F f).hom =
      eqToHom (by simp [Function.leftInverse_invFun f.injective i]) ≫ factorThruCImage F i := by
  simp only [extendIso, CospanMonoFactorisation.extend_I, Iso.symm_hom, cImage.ext_inv]
  fapply Mono.right_cancellation (f := ((cImage.cospanMonoFactorisation F).extend f).m)
  rw [Category.assoc, cImage.lift_fac]
  simp [← eqToHom_naturality (g := fun _ ↦ Y) F (Function.leftInverse_invFun f.injective i)]

@[reassoc]
lemma factorThruCImage_extendIso_hom_notMem (j : J) (h : ¬ ∃ i, f i = j) :
    factorThruCImage (F <| invFun f ·) j ≫ (extendIso F f).hom =
      eqToHom (by simp [Function.invFun_neg h]) ≫ factorThruCImage F ‹Nonempty I›.some := by
  simp only [extendIso, CospanMonoFactorisation.extend_I, Iso.symm_hom, cImage.ext_inv]
  fapply Mono.right_cancellation (f := ((cImage.cospanMonoFactorisation F).extend f).m)
  rw [Category.assoc, cImage.lift_fac]
  simp [← eqToHom_naturality (g := fun _ ↦ Y) F (Function.invFun_neg h)]

@[reassoc (attr := simp)]
lemma factorThruCImage_extendIso_inv (i : I) :
    factorThruCImage F i ≫ (extendIso F f).inv =
      eqToHom (by simp [Function.leftInverse_invFun f.injective i]) ≫
        factorThruCImage (F <| invFun f ·) (f i) := by
  rw [Iso.comp_inv_eq]; simp

end extendIso

end HasCospanImage

/-- `HasCospanImagesOfShape J C` asserts that, for every cospan `F : (i : J) → X i ⟶ Y`, there
exists a cospan image `cImage F` in `C`. -/
class HasCospanImagesOfShape (J : Type w) (C : Type u) [Category.{v} C] where
  hasCospanImage {X : J → C} {Y : C} (F : (i : J) → X i ⟶ Y) : HasCospanImage F := by
    infer_instance

instance (priority := 100) {J} [HasCospanImagesOfShape J C] {X : J → C} {Y : C}
    (F : (i : J) → X i ⟶ Y) : HasCospanImage F := ‹HasCospanImagesOfShape J C›.hasCospanImage F

namespace HasCospanImagesOfShape
open Set Function
variable {I J : Type w} [Nonempty I] (f : I ↪ J) [HasCospanImagesOfShape J C]

/-- If we have a cospan image for every cospan of a given shape, then we have a cospan image for
every smaller shape, which we express as an embedding of the index type. -/
def ofEmbedding : HasCospanImagesOfShape I C where
  hasCospanImage {X Y} F := by
    let F' (j : J) : X (invFun f j) ⟶ Y := F (invFun f j)
    have im_F' : HasCospanImage F' := inferInstance
    fapply HasCospanImage.mk; fconstructor
    · exact cImage.cospanMonoFactorisation F' |>.restrict f
    · exact cImage.isCospanImage F' |>.restrict f


-- /-- The images produced via `ofEmbedding` -- by duplicating some arbitrary morphism of the cospan --
-- are isomorphic to the images of their original cospans. -/
-- def ofEmbedding_iso {I J : Type w} [Nonempty I] (f : I ↪ J) [HasCospanImagesOfShape J C]
--     {X : I → C} {Y : C} (F : (i : I) → X i ⟶ Y) :
--     have
--     cImage (fun i ↦ F (invFun f i)) ≅ cImage F where
--   hom := cImage.lift (F := fun i ↦ F (f i))
--   inv := cImage.lift (F := F)
--   hom_inv_id := by
--     ext i
--     simp [cImage.lift_fac (F := fun i ↦ F (f i))]

/-- If we have a cospan image for every cospan of a nonempty shape, then we have normal images. -/
def hasImages {J : Type w} [hJ : Nonempty J] [HasCospanImagesOfShape J C] : HasImages C where
  has_image {_ _} f := HasCospanImagesOfShape.ofEmbedding (Function.Embedding.punit hJ.some)
    |>.hasCospanImage (fun _ ↦ f) |>.toSingleton

end HasCospanImagesOfShape


variable (F) in
/-- A `StrongEpiCospanMonoFactorisation` is a `CospanMonoFactorisation` where the factored cospan
is strongly epi. -/
structure StrongEpiCospanMonoFactorisation extends CospanMonoFactorisation F where
  /-- The factored cospan is strongly epi. -/
  [strongEpi : StrongEpiCospan E]

noncomputable def StrongEpiCospanMonoFactorisation.isCospanImage
    (fac : StrongEpiCospanMonoFactorisation F) : IsCospanImage fac.toCospanMonoFactorisation where
  lift fac' :=
      have := fac'.m_mono
      fac.strongEpi.cLift (κ := PUnit) (P := fac'.E) (Q := fun _ ↦ fac'.m)
        (G := fun _ ↦ fac.m) _ <| by rintro i ⟨⟩; constructor; simp
  lift_fac fac' := by
    have := fac'.m_mono
    simpa using fac.strongEpi.cLift_comp ⟨⟩

noncomputable def StrongEpiCospanMonoFactorisation.toCospanImageFactorisation
    (fac : StrongEpiCospanMonoFactorisation F) : CospanImageFactorisation F where
  fac := fac.toCospanMonoFactorisation
  isCospanImage := fac.isCospanImage

class HasStrongEpiCospanImagesOfShape
    (J : Type w) (C : Type u) [Category.{v} C] extends HasCospanImagesOfShape J C where
  strong_factorThruCImage {X : J → C} {Y : C} (F : (i : J) → X i ⟶ Y) :
    StrongEpiCospan (factorThruCImage F)

attribute [instance] HasStrongEpiCospanImagesOfShape.strong_factorThruCImage

def HasCospanImagesOfShape.mk'
    {J : Type w} {C : Type u} [Category.{v} C]
    (fac : ∀ {X : J → C} {Y : C} (F : (i : J) → X i ⟶ Y), StrongEpiCospanMonoFactorisation F) :
    HasCospanImagesOfShape J C :=
  ⟨(⟨⟨fac · |>.toCospanImageFactorisation⟩⟩)⟩

omit [HasCospanImage F] in
/-- If any cospan image factorisation is a `StrongEpiCospanMonoFactorisation`, then every
factorisation of the image is a strong-epi-cospan-mono factorisation. -/
lemma strongEpiCospan_of_strongEpiCospanMonoFactorisation
    (fac : StrongEpiCospanMonoFactorisation F) {fac' : CospanMonoFactorisation F}
    (h : IsCospanImage fac') : StrongEpiCospan fac'.E := by
  let fac_img := fac.isCospanImage
  convert_to StrongEpiCospan (fac.E · ≫ fac_img.lift fac')
  · ext i
    apply fac'.m_mono.right_cancellation _ _
    simp [fac_img]
  · -- TODO make this automatic
    have : IsIso (fac_img.lift fac') := instIsIsoLiftOfIsCospanImage _ h
    have := fac.strongEpi
    exact StrongEpiCospan.of_comp_iso _ _

def HasStrongEpiCospanImagesOfShape.mk'
    {J : Type w} {C : Type u} [Category.{v} C]
    (fac : ∀ {X : J → C} {Y : C} (F : (i : J) → X i ⟶ Y), StrongEpiCospanMonoFactorisation F) :
    HasStrongEpiCospanImagesOfShape J C :=
  have := HasCospanImagesOfShape.mk' fac
  ⟨fun {_ _} F ↦ strongEpiCospan_of_strongEpiCospanMonoFactorisation (fac F) <|
    cImage.isCospanImage F⟩

namespace HasStrongEpiCospanImagesOfShape

variable {J : Type w} {C : Type u} [Category.{v} C] [HasEqualizers C] [HasCospanImagesOfShape J C]

open Function in
def ofEmbedding {I J : Type w} [Nonempty I] (f : I ↪ J) [HasStrongEpiCospanImagesOfShape J C] :
    HasStrongEpiCospanImagesOfShape I C where
  hasCospanImage {X Y} F := HasCospanImagesOfShape.ofEmbedding f |>.hasCospanImage F
  strong_factorThruCImage {X Y} F := by
    have := HasCospanImagesOfShape.ofEmbedding f |>.hasCospanImage F
    let F' (j : J) : X (invFun f j) ⟶ Y := F (invFun f j)
    have im_F' : StrongEpiCospan (factorThruCImage F') := inferInstance
    fapply StrongEpiCospan.mk (llp := ?llp)
    · intro κ _ Y' X' Q _
      fapply HasCommonLiftingProperty.mk
      intro P G sq
      let P' (j : J) := P (invFun f j)
      let lift := StrongEpiCospan.cLift (factorThruCImage F') Q (P := P')
        (G := ((HasCospanImage.extendIso F f).hom ≫ G ·)) <| by
          rintro j k
          constructor
          by_cases hj : ∃ i, f i = j
          · rcases hj with ⟨i, rfl⟩
            simp [P', sq _ k |>.w, F', ← eqToHom_naturality_assoc (g := fun _ ↦ cImage F)
              (factorThruCImage F) (leftInverse_invFun f.injective i) (G k)]
          · simp [P', sq _ k |>.w, F',
            HasCospanImage.factorThruCImage_extendIso_hom_notMem_assoc F f j hj,
            ← eqToHom_naturality_assoc (g := fun _ ↦ cImage F)
              (factorThruCImage F) (Function.invFun_neg hj) (G k)]
      fapply HasCommonLift.mk
      · exact (HasCospanImage.extendIso F f).inv ≫ lift
      · intro i
        simp only [HasCospanImage.factorThruCImage_extendIso_inv_assoc, lift, P']
        rw [StrongEpiCospan.comp_cLift,
        ← eqToHom_naturality P (leftInverse_invFun f.injective i).symm]
        simp
      · intro k; simp [lift]


end HasStrongEpiCospanImagesOfShape






-- namespace StrongEpiCospanMonoFactorisation
-- variable {F} [StrongEpiCospanMonoFactorisation F]

-- namespace HasCospanImage
-- variable {F} [HasCospanImage F]



end CategoryTheory.Limits

#min_imports



-- /-- For a category `C`, `Family C` is the category of indexed families of objects in `C` for
-- varying index types. -/
-- structure Family where
--   ι : Type w
--   obj : ι → C

-- namespace Family

-- instance : CoeFun (Family C) (·.ι → C) := ⟨(·.obj)⟩

-- open Lean PrettyPrinter.Delaborator SubExpr in
-- /-- Delaborate `Family.obj` as function application. -/
-- @[app_delab Family.obj]
-- def delabFamilyObj : Delab := whenPPOption getPPNotation <| withOverApp 3 do
--   let e ← getExpr
--   guard <| e.isAppOfArity ``Family.obj 3
--   let obj ← withNaryArg 1 delab
--   let idx ← withNaryArg 2 delab
--   `($obj $idx)

-- end Family


-- variable {C}

-- /-- For a category `C` and families `X Y : Family C`, `Matrix X Y` is the type of collections
-- of morphisms `X i ⟶ Y j`.

-- Implemented as a one-field structure to avoid defeq issues. -/
-- structure Matrix (X Y : Family C) where
--   coe : (i : X.ι) → (j : Y.ι) → Set (X i ⟶ Y j)

-- instance {X Y : Family C} :
--   CoeFun (Matrix X Y) (fun _ ↦ (i : X.ι) → (j : Y.ι) → Set (X i ⟶ Y j)) := ⟨(·.coe)⟩

-- @[ext]
-- lemma Matrix.ext {X Y : Family C} {F G : Matrix X Y} (h : ∀ i j, F i j = G i j) : F = G := by
--   cases F; cases G
--   congr
--   funext i j
--   exact h i j

-- namespace Family

-- open scoped Classical in
-- @[simps -isSimp]
-- instance : Category (Family C) where
--   Hom := Matrix
--   id X := ⟨fun i j ↦ if h : i = j then { eqToHom (congrArg X h) } else ∅⟩
--   comp {X Y Z} F G := ⟨fun i k ↦ { f.1 ≫ g.1 | (j : Y.ι) (f : F i j) (g : G j k) }⟩
--   assoc {X Y Z W} F G H := by
--     ext i l _
--     constructor
--     · rintro ⟨k, ⟨_, j, f, g, rfl⟩ , h, rfl⟩
--       simpa using ⟨j, f, f.2, (g.1 ≫ h.1), ⟨k, g, g.2, h, h.2, rfl⟩, rfl⟩
--     · rintro ⟨j, f, ⟨_, k, g, h, rfl⟩, rfl⟩
--       simpa using ⟨k, (f.1 ≫ g.1), ⟨j, f, f.2, g, g.2, rfl⟩, h, h.2, Category.assoc _ _ _⟩

-- -- #check comp_coe

-- -- lemma comp_coe {X Y Z : Family C} (F : X ⟶ Y) (G : Y ⟶ Z) (i j) :
-- --     (F ≫ G) i j = { f.1 ≫ g.1 | (k : Y.ι) (f : F i k) (g : G k j) } := rfl

-- instance {X Y : Family C} :
--   CoeFun (X ⟶ Y) (fun _ ↦ (i : X.ι) → (j : Y.ι) → Set (X i ⟶ Y j)) := ⟨(·.coe)⟩

-- namespace Hom

-- @[ext]
-- lemma ext {X Y : Family C} {F G : X ⟶ Y} (h : ∀ i j, F i j = G i j) : F = G := Matrix.ext h

-- end Hom

-- /-- Promote an object `X` to a singleton family. -/
-- @[simps]
-- def single (X : C) : Family C := ⟨PUnit, fun _ ↦ X⟩

-- instance : Coe C (Family C) := ⟨single⟩

-- instance {X : C} : Unique (single X).ι := inferInstanceAs (Unique PUnit)

-- /-- Promote a morphism `f : X ⟶ Y` to a singleton matrix. -/
-- @[simps]
-- def singleHom {X Y : C} (f : X ⟶ Y) : single X ⟶ single Y := ⟨fun _ _ ↦ {f}⟩

-- instance {X Y : C} : Coe (X ⟶ Y) (single X ⟶ single Y) := ⟨singleHom⟩

-- lemma mem_singleHom {X Y : C} (f : X ⟶ Y) i j : f ∈ singleHom f i j := by simp

-- end Family
-- open Family

-- /-! Following Shulman, we refer to matrices with exactly one element between each pair of objects
-- as *arrays*. An array with a single source is a *cone*; an array with a single target is a
-- *cocone*.

-- Most of the time, we will want to work with arrays. -/

-- -- We define an array using a simple exists-unique predicate. This allows some ambiguity, as now any
-- -- matrix can be thought of as an array by introducing duplicates of each index and evenly distributing
-- -- morphisms across the duplicates. Rather than fight it, we shall take advantage of it: arrays do not
-- -- technically form a category (as they are not generally closed under composition), but a sufficiently
-- -- convenient method of turning matrices into arrays allows us to treat them as essentially
-- -- categorical.-/

-- /-- An array is a matrix with exactly one morphism between each pair of objects. -/
-- class Array ⦃X Y : Family C⦄ (F : X ⟶ Y) : Prop where
--   exists_unique : ∀ i j, ∃! f, f ∈ F i j

-- -- /-- An array is a matrix with exactly one morphism between each pair of objects. -/
-- -- def arrays : MorphismProperty (Family C) := Array

-- namespace Array

-- instance {X Y : C} (f : X ⟶ Y) : Array (singleHom f) where
--   exists_unique i j :=
--     ⟨f, by simp [single_obj, singleHom, comp_coe], by simp [single_obj, singleHom, comp_coe]⟩

-- noncomputable def toPi {X Y : Family C} (F : X ⟶ Y) [h : Array F] i j :=
--   h.exists_unique i j |>.choose

-- @[simp]
-- lemma toPi_mem {X Y : Family C} (F : X ⟶ Y) [h : Array F] i j : toPi F i j ∈ F i j :=
--   h.exists_unique i j |>.choose_spec.1

-- @[simp]
-- lemma coe_eq_toPi {X Y : Family C} (F : X ⟶ Y) [h : Array F] i j : F i j = {toPi F i j} := by
--   ext f
--   have := h.exists_unique i j |>.choose_spec.2
--   constructor --<;> intro h
--   · intro h; simp [this _ h, toPi]
--   · rintro ⟨⟩; exact toPi_mem F i j

-- @[simp]
-- lemma singleHom_toPi {X Y : C} (f : X ⟶ Y) i j : toPi (singleHom f) i j = f := by
--   have : Array (singleHom f) := inferInstance
--   have := this.exists_unique i j |>.choose_spec.2 f (mem_singleHom f i j)
--   conv_rhs => rw [this]
--   simp [single_obj, singleHom, toPi]

-- /-- Convenience constructor for turning a family of morphisms with common source into an cone. -/
-- @[simps]
-- def ofπ {ι} {X : C} {Y : ι → C} (f : (i : ι) → X ⟶ Y i) : ↑X ⟶ Family.mk ι Y :=
--   ⟨fun _ j ↦ { f j }⟩

-- instance {ι} {X : C} {Y : ι → C} (f : (i : ι) → X ⟶ Y i) : Array (ofπ f) where
--   exists_unique i j := ⟨f j, by simp [Array.ofπ], by simp [Array.ofπ]⟩

-- /-- Convenience constructor for turning a family of morphisms with common target into an cocone. -/
-- @[simps]
-- def ofι {ι} {X : ι → C} {Y : C} (f : (i : ι) → X i ⟶ Y) : Family.mk ι X ⟶ ↑Y :=
--   ⟨fun i _ ↦ { f i }⟩

-- instance {ι} {X : ι → C} {Y : C} (f : (i : ι) → X i ⟶ Y) : Array (ofι f) where
--   exists_unique i j := ⟨f i, by simp [Array.ofι], by simp [Array.ofι]⟩

-- /-- Convenience projection for turning arrays between singletons into morphisms. -/
-- @[simp]
-- noncomputable def toHom {x y : C} (F : single x ⟶ single y) [h : Array F] := h.toPi F ⟨⟩ ⟨⟩


-- /-- Convenience projection for turning cones into indexed families of morphisms with a common
-- source. -/
-- noncomputable def π {x : C} {Y : Family C} (F : ↑x ⟶ Y) [h : Array F] (j : Y.ι) :=
--   toPi F ⟨⟩ j

-- lemma π_mem {x : C} {Y : Family C} (F : ↑x ⟶ Y) [h : Array F] (j : Y.ι) :
--   π F j ∈ F ⟨⟩ j := toPi_mem F ⟨⟩ j

-- @[simp]
-- lemma π_ofπ {ι} {X : C} {Y : ι → C} (f : (i : ι) → X ⟶ Y i) (j : ι) :
--     π (ofπ f) j = f j := by
--   have : Array (ofπ f) := inferInstance
--   simp only [single_obj, π, ofπ, single_ι]
--   rw [this.exists_unique ⟨⟩ j |>.choose_spec.2 (f j), toPi]; rfl

-- /-- Convenience projection for turning cocones into indexed families of morphisms with a common
-- target. -/
-- noncomputable def ι {X : Family C} {y : C} (F : X ⟶ y) [h : Array F] (i : X.ι) := toPi F i ⟨⟩

-- lemma ι_mem {X : Family C} {y : C} (F : X ⟶ y) [h : Array F] (i : X.ι) :
--   ι F i ∈ F i ⟨⟩ := toPi_mem F i ⟨⟩

-- @[simp]
-- lemma ι_ofι {ι} {X : ι → C} {Y : C} (f : (i : ι) → X i ⟶ Y) (i : ι) :
--     Array.ι (ofι f) i = f i := by
--   have : Array (ofι f) := inferInstance
--   simp only [single_obj, Array.ι, ofι, single_ι]
--   rw [this.exists_unique i ⟨⟩ |>.choose_spec.2 (f i), toPi]; rfl

-- end Array

-- namespace Matrix

-- export Array (toPi ofπ ofι toHom π ι)

-- end Matrix


-- -- def cones : MorphismProperty (Family C) :=
-- --   fun ⦃X _⦄ F ↦ arrays F ∧ Nonempty (Unique X.ι)

-- -- noncomputable def cones.π {x : C} {Y : Family C} (F : ↑x ⟶ Y) (h : arrays F) (j : Y.ι) :=
-- --   h.toPi ⟨⟩ j

-- -- noncomputable def cones.π' {X Y : Family C} (F : X ⟶ Y) (h : cones F) (j : Y.ι) :=
-- --   h.1.toPi h.2.some.default j

-- -- def cocones : MorphismProperty (Family C) :=
-- --   fun ⦃_ Y⦄ F ↦ arrays F ∧ Nonempty (Unique Y.ι)

-- -- noncomputable def cocones.ι {X : Family C} {x : C} (F : X ⟶ ↑x) (h : arrays F) (i : X.ι) :=
-- --   h.toPi i ⟨⟩

-- -- noncomputable def cocones.ι' {X Y : Family C} (F : X ⟶ Y) (h : cocones F) (i : X.ι) :=
-- --   h.1.toPi i h.2.some.default

-- namespace Array

-- /-- A nonempty cocone is an effective epi in `Family C` iff it is an effective epi family in `C`. -/
-- lemma effectiveEpi_iff {X : Family C} [Nonempty X.ι] {y : C} (F : X ⟶ y) [h : Array F] :
--   EffectiveEpi F ↔ EffectiveEpiFamily (B := y) X F.ι where
--   mp hF := ⟨⟨{
--     desc {w} e he := by?
--       have hd {Z} (G₁ G₂ : Z ⟶ X) (hG : G₁ ≫ F = G₂ ≫ F) : G₁ ≫ ofι e = G₂ ≫ ofι e := by
--         rw [Hom.ext_iff] at hG ⊢
--         intro i ⟨⟩
--         specialize hG i ⟨⟩
--         rw [Set.ext_iff] at hG
--         ext f
--         simp only [single_obj, comp_coe, ofι_coe, Subtype.exists, Set.mem_singleton_iff,
--           exists_prop, exists_eq_left, Set.mem_setOf_eq]
--         constructor
--         · rintro ⟨j, f, hf, rfl⟩
--           specialize hG (f ≫ F.ι j)
--           replace he a₁ g₁ := he a₁ j g₁ f
--           simp only [single_obj, comp_coe, Subtype.exists, coe_eq_toPi, Set.mem_singleton_iff,
--             exists_prop, exists_eq_left, Set.mem_setOf_eq] at hG
--           obtain ⟨j', g, hg, h'⟩ := hG.mp ⟨_, f, hf, rfl⟩
--           simp_rw [← ι.eq_def] at h'
--           use j', g, hg
--           fapply he; exact h'
--         · rintro ⟨j', g, hg, rfl⟩
--           specialize hG (g ≫ F.ι j')
--           simp only [single_obj, comp_coe, Subtype.exists, coe_eq_toPi, Set.mem_singleton_iff,
--             exists_prop, exists_eq_left, Set.mem_setOf_eq] at hG
--           obtain ⟨j, f, hf, h'⟩ := hG.mpr ⟨_, g, hg, rfl⟩
--           simp_rw [← ι.eq_def] at h'
--           use j, f, hf
--           fapply he; exact h'
--       letI d : single y ⟶ single w := hF.desc _ (ofι e) hd
--       have fac : ∀ i, (∃ a ∈ d ⟨⟩ ⟨⟩, ι F i ≫ a = e i) ∧ ∀ a ∈ d ⟨⟩ ⟨⟩, ι F i ≫ a = e i := by
--         simpa [comp_coe, ← ι.eq_def, -EffectiveEpi.fac, Set.eq_singleton_iff_unique_mem,
--         Unique.forall_iff, Unique.exists_iff, Hom.ext_iff] using hF.fac _ (ofι e) hd
--       have : Array d := by
--         stop
--         constructor
--         rintro ⟨⟩ ⟨⟩
--         refine ⟨?_, ?_, ?_⟩
--         · have : (d ⟨⟩ ⟨⟩).Nonempty := by
--             by_contra! h!
--             specialize fac <| Nonempty.some ‹_›
--             simp [funext_iff, comp_coe, h!, Set.singleton_ne_empty _ |>.symm] at fac
--           exact this.some
--         · lift_lets
--           intro this
--           simp [this.some_mem]
--         · rintro f hf
--           have := hF.uniq _ (ofι e) hd (singleHom f) <| by
--             ext i ⟨⟩ f'
--             replace fac := fac i |>.2 f hf
--             simp [comp_coe, ← ι.eq_def, Unique.exists_iff, ← fac]
--           simp_rw [Hom.ext_iff, Unique.forall_iff, singleHom_coe] at this
--           symm at this ⊢
--           simp [Set.eq_singleton_iff_unique_mem] at this
--           fapply this.2
--           lift_lets; intro this; exact this.some_mem
--       exact eqToHom (by simp) ≫ Array.toHom d ≫ eqToHom (by simp)
--     fac {W} e he i := by
--       lift_lets
--       intro hd fac _; clear_value hd fac
--       simp [fac i |>.2]
--     uniq {W} e he f hf := by
--       lift_lets
--       intro hd fac _; clear_value hd fac
--       have uniq := hF.uniq _ (ofι e) hd (singleHom f) <| by
--         ext i ⟨⟩ f'
--         simp [comp_coe, ← ι.eq_def, Unique.exists_iff, hf]
--       simp [← uniq]
--   }⟩⟩
--   mpr hF := ⟨⟨{
--     desc {W} E hE := by?
--       fapply ofπ
--       intro i
--       fapply hF.desc _ _-- E.toPi
--       -- have hd {Z} (G₁ G₂ : Z ⟶ X) (hG : G₁ ≫ F = G₂ ≫ F) : G₁ ≫ ofι e = G₂ ≫ ofι e := by
--       --   rw [Hom.ext_iff] at hG ⊢
--       --   intro i ⟨⟩
--       --   specialize hG i ⟨⟩
--   }⟩⟩
