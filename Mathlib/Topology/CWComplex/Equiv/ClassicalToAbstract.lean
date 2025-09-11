/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/

import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Instances.Shrink
import Mathlib.Topology.Category.TopCat.EffectiveEpi
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Mathlib.CategoryTheory.EffectiveEpi.Coproduct
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
-- import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.Category.Cat.Colimit
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.CategoryTheory.Limits.Fubini

import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.Logic.Equiv.PartialEquiv
import Qq


-- import Mathlib.Tactic.LiftLets
import Mathlib.Tactic.Peel
import Mathlib.Tactic.Widget.CommDiag
import Mathlib.Tactic.ENatToNat
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.Panel.GoalTypePanel

/-!
  # The abstract and classical definitions of CW-complexes coincide.
  Specifically, in this file we show that the abstract `TopCat.RelativeCWComplex` structure
  can be built from any concrete `Topology.RelCWComplex`, so long as the ambient space of the
  latter is T2.
-/

universe w' w t v' v u' u

open TopCat CategoryTheory Limits HomotopicalAlgebra Set ContinuousMap Set.Notation TopologicalSpace
open scoped Set.Notation ENat

@[simps!]
def WithTop.functor α [Preorder α] : α ⥤ WithTop α :=
  Monotone.functor fun {_ _} ↦ WithTop.coe_le_coe.mpr

-- @[simps!]
-- def ENat.ofNatFunctor : ℕ ⥤ ℕ∞ :=
--   Monotone.functor fun {_ _} ↦ WithTop.coe_le_coe.mpr

#check Homeomorph.mk

-- open Function in
-- @[simps]
-- def Homeomorph.ofContinuousMaps {X Y} [TopologicalSpace X] [TopologicalSpace Y]
--     (toFun : C(X, Y)) (invFun : C(Y, X))
--     (left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl)
--     (right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl) : X ≃ₜ Y where
--   toFun
--   invFun
--   left_inv
--   right_inv

-- namespace Set
-- variable {α : Type*} {s t : Set α}

-- /-- When `s ⊆ t`, `Set.inclusion` can be lifted into a map into `t ↓∩ s`. -/
-- def inclusionPreimageVal (h : s ⊆ t) : s → t ↓∩ s := fun x ↦ ⟨Set.inclusion h x, by simp⟩

-- @[simp]
-- lemma inclusionPreimageVal_mk (h : s ⊆ t) (x : α) (hx : x ∈ s) :
--     inclusionPreimageVal h ⟨x, hx⟩ = ⟨⟨x, h hx⟩, hx⟩ := rfl

-- @[simp, higher_order val_comp_inclusionPreimageVal]
-- lemma val_inclusionPreimageVal (h : s ⊆ t) (x : s) :
--     Subtype.val (inclusionPreimageVal h x) = Set.inclusion h x := rfl

-- attribute [simp] val_comp_inclusionPreimageVal


-- variable (s t) in
-- /-- The 'identity' function recognizing values of the intersection `s ↓∩ t` as values of `t`. -/
-- @[simp]
-- def preimageValInclusion : s ↓∩ t → t := fun x ↦ ⟨x, by simpa [-Subtype.coe_prop] using x.2⟩

-- /-- When `s ⊆ t`, `s ≃ t ↓∩ s`. -/
-- @[simps]
-- def _root_.Equiv.Set.preimageVal (h : s ⊆ t) : s ≃ t ↓∩ s where
--   toFun := inclusionPreimageVal h
--   invFun := preimageValInclusion _ _

-- end Set

-- namespace ContinuousMap

-- /-- `Continuous.subtype_val` bundled into a continuous map. -/
-- @[simps]
-- def subtypeVal {X : Type*} [TopologicalSpace X]
--     {p : X → Prop} : C(Subtype p, X) where
--   toFun := Subtype.val

-- /-- Given a function `f : α → β` s.t. `MapsTo f s t`, if `f` is continuous on `s` then `f` can
-- be lifted into a continuous map from `s` to `t`. -/
-- @[simps -fullyApplied]
-- def mapsTo {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
--     (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) (hf : ContinuousOn f s) : C(s, t) where
--   toFun := MapsTo.restrict f s t h
--   continuous_toFun := ContinuousOn.restrict_mapsTo hf _

-- -- lemma mapsTo_surjective {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
-- --     (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) (hf : ContinuousOn f s) :
-- --     Function.Surjective (mapsTo f s t h hf) := by
-- --   unfold mapsTo
-- --   simp?

-- /-- The 'identity' function recognizing values of the intersection `s ↓∩ t` as values of `t`,
-- as a continuous map.. -/
-- @[simp]
-- def preimageValIncl {X : Type*} [TopologicalSpace X] (s t : Set X) : C(s ↓∩ t, t) where
--   toFun := preimageValInclusion s t
--   continuous_toFun := by unfold preimageValInclusion; continuity

-- /-- When `s ⊆ t`, the inclusion of `s` into `t` can be lifted into a continuous map`C(s, t ↓∩ s)`.
-- -/
-- @[simps]
-- def inclPreimageVal {X : Type*} [TopologicalSpace X] {s t : Set X}
--     (h : s ⊆ t) : C(s, t ↓∩ s) where
--   toFun := inclusionPreimageVal h
--   continuous_toFun := Continuous.subtype_mk (continuous_inclusion _) _

-- /-- When `s ⊆ t`, `s ≃ₜ t ↓∩ s`. -/
-- @[simps]
-- def _root_.Homeomorph.Set.preimageVal {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s ⊆ t) :
--     s ≃ₜ t ↓∩ s where
--   toFun := inclPreimageVal h
--   invFun := preimageValIncl t s
--   continuous_invFun := ContinuousMap.continuous _

-- @[simp]
-- def mk_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
--     (hf : Continuous f) (x : X) : { toFun := f, continuous_toFun := hf : C(X, Y) } x = f x:= by rfl

-- def inl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : C(X, X ⊕ Y) where
--   toFun := Sum.inl
--   continuous_toFun := by continuity

-- @[simp]
-- lemma coe_inl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
--     ⇑(inl : C(X, X ⊕ Y)) = Sum.inl := rfl

-- def inr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : C(Y, X ⊕ Y) where
--   toFun := Sum.inr
--   continuous_toFun := by continuity

-- @[simp]
-- lemma coe_inr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
--     ⇑(inr : C(Y, X ⊕ Y)) = Sum.inr := rfl

-- /-- A continuous map from a sum can be defined by its action on the summands.
-- This is `Continuous.sumElim` bundled into a continuous map. -/
-- @[simps]
-- def sum {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
--     (f : C(X, Z)) (g : C(Y, Z)) : C(X ⊕ Y, Z) where
--   toFun := fun x ↦ Sum.elim f.toFun g.toFun x
--   continuous_toFun := Continuous.sumElim f.continuous g.continuous

-- @[simp]
-- lemma sum_comp_inl {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
--     (f : C(X, Z)) (g : C(Y, Z)) : (sum f g) ∘ Sum.inl = f := by
--   ext x; simp

-- @[simp]
-- lemma sum_comp_inr {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
--     (f : C(X, Z)) (g : C(Y, Z)) : (sum f g) ∘ Sum.inr = g := by
--   ext x; simp


-- /-- A continuous map between sums can be defined fiberwise by its action on the summands.
-- This is `Continuous.sumMap` bundled into a continuous map. -/
-- @[simps]
-- def sumMap {X Y Z W : Type*}
--     [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
--     (f : C(X, Z)) (g : C(Y, W)) : C(X ⊕ Y, Z ⊕ W) where
--   toFun := Sum.map f g

-- @[simp]
-- lemma sumMap_comp_inl {X Y Z W : Type*}
--     [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
--     (f : C(X, Z)) (g : C(Y, W)) : (sumMap f g) ∘ Sum.inl = Sum.inl ∘ f := by
--   ext x; simp

-- @[simp]
-- lemma sumMap_comp_inr {X Y Z W : Type*}
--     [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
--     (f : C(X, Z)) (g : C(Y, W)) : (sumMap f g) ∘ Sum.inr = Sum.inr ∘ g := by
--   ext x; simp

-- /-- A continuous map between sigma types can be defined fiberwise by its action on the summands.
-- This is `Continuous.sigma_map` bundled into a continuous map. -/
-- @[simps]
-- def sigmaMap {ι κ : Type*} {σ : ι → Type*} {τ : κ → Type*}
--     [(i : ι) → TopologicalSpace (σ i)] [(k : κ) → TopologicalSpace (τ k)]
--     (f₁ : ι → κ) (f₂ : (i : ι) → C(σ i, τ (f₁ i))) : C(Sigma σ, Sigma τ) where
--   toFun := (Sigma.map f₁ (f₂ ·))

-- @[simp]
-- lemma sigmaMap_comp_mk {ι κ : Type*} {σ : ι → Type*} {τ : κ → Type*}
--     [(i : ι) → TopologicalSpace (σ i)] [(k : κ) → TopologicalSpace (τ k)]
--     (f₁ : ι → κ) (f₂ : (i : ι) → C(σ i, τ (f₁ i))) (i : ι) :
--     (sigmaMap f₁ f₂).comp (sigmaMk i) = (sigmaMk (f₁ i)).comp (f₂ i) := by
--   ext x <;> simp [Sigma.map]

-- lemma sigma_comp_mk
--     {I A} {X : I → Type*} [TopologicalSpace A] [(i : I) → TopologicalSpace (X i)]
--     (f : (i : I) → C(X i, A)) (i : I) : (sigma f).comp (sigmaMk i) = f i := by
--   ext x
--   simp

-- lemma coe_sigmaMk {I} {X : I → Type*} [(i : I) → TopologicalSpace (X i)] (i : I) :
--   ⇑(sigmaMk (X := X) i) = Sigma.mk i := rfl

-- @[simp]
-- lemma coe_inclusion {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s ⊆ t) :
--   ⇑(inclusion h) = Set.inclusion h := rfl

-- end ContinuousMap



-- lemma IsEmbedding.inclPreimageVal {X : Type*} [TopologicalSpace X] {s t : Set X}
--     (h : s ⊆ t) : Topology.IsEmbedding (inclPreimageVal h) where
--   eq_induced := by
--     ext u
--     simp_rw [isOpen_induced_iff, ContinuousMap.inclPreimageVal, ContinuousMap.coe_mk]
--     unfold inclusionPreimageVal
--     simp [preimage_preimage]
--   injective x y heq := by simpa [inclusionPreimageVal, Subtype.val_inj] using heq

-- lemma isOpen_sup_iff {α : Type u} {S T : TopologicalSpace α} {s : Set α} :
--     @IsOpen α (S ⊔ T) s ↔ @IsOpen α S s ∧ @IsOpen α T s := by
--   constructor <;> (rintro ⟨hL, hR⟩; exact ⟨hL, hR⟩)

-- lemma isClosed_sup_iff {α : Type u} {S T : TopologicalSpace α} {s : Set α} :
--     @IsClosed α (S ⊔ T) s ↔ @IsClosed α S s ∧ @IsClosed α T s := by
--   simp_rw [← isOpen_compl_iff]
--   exact isOpen_sup_iff

lemma coinduced_inclusion_eq_coinduced_val
    {X : Type u} [TopologicalSpace X] {s t : Set X} (h : s ⊆ t) :
    coinduced (Set.inclusion h) instTopologicalSpaceSubtype =
      coinduced ((↑) : t ↓∩ s → t) instTopologicalSpaceSubtype := by
  let η := Topology.IsEmbedding.inclPreimageVal h |>.toHomeomorphOfSurjective <|
    Equiv.Set.preimageVal h |>.surjective
  suffices Set.inclusion h = Subtype.val ∘ η by rw [this, ← coinduced_compose, η.coinduced_eq]
  ext x; simp [η]


lemma coinduced_inclPreimageVal {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s ⊆ t) :
    coinduced (inclPreimageVal h) instTopologicalSpaceSubtype =
      instTopologicalSpaceSubtype := by
  symm
  unfold instTopologicalSpaceSubtype
  simp_rw [induced_compose]
  ext u
  constructor
  · rintro ⟨u', u'_open, hu'⟩
    use u', u'_open
    rw [Set.ext_iff] at hu' ⊢
    simp at hu' ⊢
    solve_by_elim
  · rintro ⟨u', u'_open, hu'⟩
    use u', u'_open
    rw [Set.ext_iff] at hu' ⊢
    simp at hu' ⊢
    solve_by_elim

lemma preimage_val_preimage_val_inter {α : Type*} {s t u : Set α} :
    (s ↓∩ t) ↓∩ (s ↓∩ (t ∩ u)) = (s ↓∩ t) ↓∩ s ↓∩ u := by
  ext x; simp

namespace Topology.RelCWComplex
variable {X : Type u} [TopologicalSpace X] (C D : Set X) [𝓔 : RelCWComplex C D]
variable {D}

-- attribute [local simp] skeletonLT_zero_eq_base

@[simps map]
def skeletonLT.asFunctor [T2Space X] : ℕ∞ ⥤ TopCat where
  obj n := of (skeletonLT C n)
  map f := ofHom <| inclusion <| skeletonLT_mono <| by simp [leOfHom f]

@[simp]
lemma skeletonLT.asFunctor_obj [T2Space X] {n : ℕ∞} :
  (skeletonLT.asFunctor C).obj n = of (skeletonLT C n) := rfl


@[simps map]
def skeleton.asFunctor [T2Space X] : ℕ∞ ⥤ TopCat where
  obj n := of (skeleton C n)
  map f := ofHom <| inclusion <| skeleton_mono <| by simp [leOfHom f]

@[simp]
lemma skeleton.asFunctor_obj [T2Space X] {n : ℕ∞} :
  (skeleton.asFunctor C).obj n = of (skeleton C n) := rfl

variable {C} in
/-- `map n j` bundled into a continuous map from the disk to its closed cell. -/
@[simps! apply]
noncomputable def map' (n : ℕ) (j : cell C n) :
    C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, closedCell n j) :=
  ContinuousMap.mapsTo (map n j) (Metric.closedBall 0 1) (closedCell n j)
    (mapsTo_image _ _) (continuousOn n j)

-- variable {C} in
-- /-- A subcomplex of a subcomplex is a subcomplex of the original complex. -/
-- @[simps]
-- def Subcomplex.incl [T2Space X] {E : Subcomplex C} (F : Subcomplex (↑E : Set X)) :
--     Subcomplex C where
--   carrier := F
--   I n := Subtype.val '' F.I n
--   closed' := F.closed
--   union' := by
--     rw [← F.union]
--     congr! with n
--     fapply (Equiv.Set.image _ _ Subtype.val_injective).symm.iSup_congr
--     · rintro ⟨_, ⟨x, hx, rfl⟩⟩
--       simp only [toComplex_cell, Equiv.Set.image_symm_apply]
--       unfold openCell
--       congr! 1


-- lemma incl_skeletonLT_skeletonLT [T2Space X] {n m : ℕ} :
--     Subcomplex.incl (skeletonLT (skeletonLT C n : Set X) m) = skeletonLT C (min n m) := by
--   ext x
--   simp_rw [← SetLike.mem_coe, Subcomplex.coe_incl, SetLike.mem_coe, mem_skeletonLT_iff]
--   constructor
--   · rintro (hx | ⟨r, hr, ⟨j, hj⟩, hx⟩)
--     · exact .inl hx
--     · simp only [skeletonLT_I, Nat.cast_lt, mem_setOf_eq] at hj
--       right
--       use r, by simp [hj, hr] at hr ⊢, j
--       simpa [openCell] using hx
--   · rintro (hx | ⟨r, hr, j, hx⟩)
--     · exact .inl hx
--     · right
--       use r, trans hr (min_le_right _ _),
--         ⟨j, by simpa [skeletonLT_I] using trans hr (min_le_left _ _)⟩
--       simpa [openCell] using hx


variable {C} in
/-- All cell frontiers are disjoint from open cells of the same or higher dimension. -/
lemma disjoint_openCell_cellFrontier {n m : ℕ} (h : m ≤ n) (j : cell C n) (k : cell C m) :
    Disjoint (openCell n j) (cellFrontier m k) := by
  -- rcases em (n = m) with rfl | h!
  · obtain ⟨I, hI⟩ := cellFrontier_subset_finite_openCell m k
    fapply disjoint_of_subset_right hI
    simp_rw [disjoint_union_right, disjoint_iUnion_right]
    split_ands
    · fapply disjoint_of_subset_left (subset_iUnion₂ _ _)
      symm
      exact disjoint_base_iUnion_openCell
    · rintro k hk i hi
      replace hk : n ≠ k := ne_of_gt (trans hk h)
      exact disjoint_openCell_of_ne (by simp [hk])
  -- · replace h := lt_of_le_of_ne' h h!

variable {C} in
/-- The open cells are open in their skeleton. (But not, in general, in the complex.) -/
lemma isOpen_openCell_skeletonLT [T2Space X] n (j : cell C n) :
    IsOpen (↑(skeletonLT C (n + 1)) ↓∩ openCell n j) := by
  rw [← isClosed_compl_iff,
  (skeletonLT C (n + 1)).toComplex.isCoherentWith_closedCells.isClosed_iff,
  -- simp_rw [(skeletonLT C (n + 1)).toComplex.isCoherentWith_closedCells.isOpen_iff,
  forall_mem_insert, forall_mem_range, Sigma.forall]
  split_ands
  · convert isClosed_univ
    simpa [preimage_eq_empty_iff] using disjointBase n j |>.preimage _
  · simp only [SetLike.coe_sort_coe, Subcomplex.toComplex_cell, skeletonLT_I, Subtype.forall,
    Set.mem_setOf, preimage_compl]
    rintro m k hk
    rw [← Nat.cast_one, ← Nat.cast_add, ENat.coe_lt_coe] at hk
    rcases em (∃ _ : m = n, k ≍ j) with ⟨⟨⟩, ⟨⟩⟩ | hjk
    · rw [← preimage_compl, ← preimage_compl,
      isClosed_closedCell.preimage_val.inter_preimage_val_iff, ← preimage_inter]
      apply IsClosed.preimage continuous_subtype_val
      rw [← cellFrontier_union_openCell_eq_closedCell, union_inter_distrib_right, inter_compl_self,
      union_empty, inter_eq_self_of_subset_left]
      · exact isClosed_cellFrontier
      · apply Disjoint.subset_compl_left
        exact disjoint_openCell_cellFrontier (le_refl _) _ _
    · rw [isClosed_compl_iff, ← preimage_val_preimage_val_inter]
      push_neg at hjk
      apply IsOpen.preimage continuous_subtype_val
      apply IsOpen.preimage continuous_subtype_val
      convert isOpen_empty
      erw [← cellFrontier_union_openCell_eq_closedCell, union_inter_distrib_right, union_empty_iff]
      split_ands
      · grw [← disjoint_iff_inter_eq_empty, cellFrontier_subset_skeletonLT]
        exact disjoint_skeletonLT_openCell (ENat.coe_le_coe.mpr <| Nat.le_of_lt_succ hk)
      · rw [← disjoint_iff_inter_eq_empty]
        simpa using pairwiseDisjoint (mem_univ ⟨m, k⟩) (mem_univ ⟨n, j⟩) (by simpa using hjk)

noncomputable def descBySkeletonLT [T2Space X] {Z} [TopologicalSpace Z]
    (f : (n : ℕ) → C(skeletonLT C n, Z))
    (hf : ∀ (n : ℕ) (x : skeletonLT C n),
      f (n + 1) (ContinuousMap.inclusion (skeletonLT_mono <| ENat.coe_le_coe.mpr <| n.le_succ) x)
        = f n x) : C(C, Z) where
  toFun := Set.iUnionLift (fun (n : ℕ) ↦ skeletonLT C n) (f ·) coherence C
      (le_of_eq iUnion_skeletonLT_eq_complex.symm)
  continuous_toFun := by
    have emb n s :
        Set.inclusion (le_of_eq 𝓔.iUnion_skeletonLT_eq_complex.symm) ⁻¹'
            (Set.inclusion (subset_iUnion _ n) '' s) =
          Set.inclusion (skeletonLT C n).subset_complex '' s := by
      ext ⟨x, hx⟩; simp
    rw [𝓔.isCoherentWith_closedCells.continuous_iff]
    rintro s (rfl | ⟨⟨n, j⟩, rfl⟩)
    all_goals
      simp_rw [continuousOn_iff_isClosed, preimage_iUnionLift]
      intro t tC
    · use (Set.inclusion <| skeletonLT C 0 |>.subset_complex) '' (f 0 ⁻¹' t),
        IsClosedEmbedding.inclusion _ (skeletonLT C 0 |>.closed.preimage <| continuous_subtype_val)
          |>.isClosed_iff_image_isClosed.mp <| tC.preimage (f 0).continuous
      simp only [SetLike.coe_sort_coe, preimage_iUnion, emb, iUnion_inter]
      rw [← union_iUnion_nat_succ]
      apply union_eq_self_of_subset_right
      rw [iUnion_subset_iff]
      rintro n x ⟨hx₁, hx₂⟩
      simp only [mem_inter_iff, mem_image, mem_preimage, Subtype.exists, inclusion_mk,
        CharP.cast_eq_zero, hx₂, and_true]
      use x, by rwa [← 𝓔.skeletonLT_zero_eq_base] at hx₂, ?_
      rcases hx₁ with ⟨x, hx, rfl⟩
      simp [← 𝓔.skeletonLT_zero_eq_base] at hx₂
      simpa [coherence 0 (n + 1) x.1 hx₂ x.2]
    · use (Set.inclusion <| skeletonLT C (n + 1) |>.subset_complex) '' (f (n + 1) ⁻¹' t),
        IsClosedEmbedding.inclusion _
            (skeletonLT C (n + 1) |>.closed.preimage <| continuous_subtype_val)
          |>.isClosed_iff_image_isClosed.mp <| tC.preimage (f (n + 1)).continuous
      simp only [SetLike.coe_sort_coe, preimage_iUnion, emb, iUnion_inter]
      rw [← Monotone.iUnion_nat_add _ (n + 1), ← union_iUnion_nat_succ, zero_add]
      · apply union_eq_self_of_subset_right
        rw [iUnion_subset_iff]
        rintro m x ⟨hx₁, hx₂⟩
        simp only [mem_inter_iff, mem_image, mem_preimage, Subtype.exists, inclusion_mk, hx₂,
        and_true]
        use x, closedCell_subset_skeletonLT n j hx₂, ?_
        rcases hx₁ with ⟨x, hx, rfl⟩
        simp at hx₂
        simpa [coherence (n + 1) _ x.1 (closedCell_subset_skeletonLT n j hx₂) x.2]
      · intro m₁ m₂ hm x
        simp only [mem_inter_iff, mem_image, mem_preimage, Subtype.exists, inclusion_mk]
        gcongr with x'
        rintro ⟨hx, hxt, rfl⟩
        have := skeletonLT_mono (ENat.coe_le_coe.mpr hm) hx
        use this, by simpa [coherence m₂ m₁ x' this hx]
where
 coherence := by
  intro n m x hx₁ hx₂
  wlog h : n < m generalizing n m
  · rcases em (n = m) with rfl | hne
    · rfl
    · symm; exact this m n hx₂ hx₁ (by omega)
  symm
  induction h with
  | refl => exact hf n ⟨x, hx₁⟩
  | @step m hm ih =>
    have : (n : ℕ∞) ≤ m := ENat.coe_le_coe.mpr <| Nat.le_of_succ_le hm
    specialize hf m ⟨x, skeletonLT_mono this hx₁⟩
    specialize ih (skeletonLT_mono this hx₁)
    simp [ContinuousMap.inclusion] at hf ih; simp [hf, ih]

lemma descBySkeletonLT_inclusion [T2Space X] {Z} [TopologicalSpace Z]
    {f : (n : ℕ) → C(skeletonLT C n, Z)} {hf} (n : ℕ) :
    (descBySkeletonLT C f hf).comp
      (ContinuousMap.inclusion (skeletonLT C n).subset_complex) = f n := by
  ext x; simp [descBySkeletonLT, ContinuousMap.inclusion]

@[simp]
lemma descBySkeletonLT_inclusion_apply [T2Space X] {Z} [TopologicalSpace Z]
    {f : (n : ℕ) → C(skeletonLT C n, Z)} {hf} (n : ℕ) x :
    descBySkeletonLT C f hf
      (ContinuousMap.inclusion (skeletonLT C n).subset_complex x) = f n x := by
  simp [descBySkeletonLT, ContinuousMap.inclusion]

lemma descBySkeletonLT_of_mem [T2Space X] {Z} [TopologicalSpace Z]
    {f : (n : ℕ) → C(skeletonLT C n, Z)} {hf} (n : ℕ) {x} (hx : x ∈ skeletonLT C n) :
    descBySkeletonLT C f hf ⟨x, (skeletonLT C n).subset_complex hx⟩ = f n ⟨x, hx⟩ := by
  simp only [descBySkeletonLT, coe_mk]
  rw [iUnionLift_of_mem (S := fun (n : ℕ) ↦ skeletonLT C n)
    ⟨x, skeletonLT C n |>.subset_complex hx⟩ hx]


/-- Equal types are homeomorphic, so long as their topologies are equal too. (This is `Equiv.cast`
as a homeomorphism.) -/
@[simps!]
def Homeomorph.cast {X Y} [instX : TopologicalSpace X] [instY : TopologicalSpace Y] (h₀ : X = Y)
    (_ : instX ≍ instY) : X ≃ₜ Y where
  __ := Equiv.cast h₀

noncomputable def descBySkeleton [T2Space X] {Z} [TopologicalSpace Z]
    (d : C(D, Z))
    (f : (n : ℕ) → C(skeleton C n, Z))
    (hd : ∀ (x : D), f 0 (ContinuousMap.inclusion (skeleton C 0).base_subset x) = d x)
    (hf : ∀ (n : ℕ) (x : skeleton C n),
      f (n + 1) (ContinuousMap.inclusion (skeleton_mono <| ENat.coe_le_coe.mpr <| n.le_succ) x)
        = f n x) : C(C, Z) :=
  descBySkeletonLT C
    (fun
    | 0 => (congrArg (fun s : Set X ↦ C(s, Z)) 𝓔.skeletonLT_zero_eq_base).mpr d
    -- d.comp <| toContinuousMap <| Homeomorph.cast (congrArg (↥) skeletonLT_zero_eq_base)
    --     (by congr; erw [𝓔.skeletonLT_zero_eq_base]; rfl)
    | n + 1 => f n)
    (fun
    | 0, x => by
      simp only [eq_mpr_eq_cast]
      -- simp_rw [skeleton.eq_def, ← Nat.succ_eq_add_one] at f
      erw [← ContinuousMap.comp_apply (f 0)]
      -- change ((f 0) ∘ _) x = _
      -- congr!

    )


lemma descBySkeletonLT_inclusion [T2Space X] {Z} [TopologicalSpace Z]
    {f : (n : ℕ) → C(skeletonLT C n, Z)} {hf} (n : ℕ) :
    (descBySkeletonLT C f hf).comp
      (ContinuousMap.inclusion (skeletonLT C n).subset_complex) = f n := by
  ext x; simp [descBySkeletonLT, ContinuousMap.inclusion]

@[simp]
lemma descBySkeletonLT_inclusion_apply [T2Space X] {Z} [TopologicalSpace Z]
    {f : (n : ℕ) → C(skeletonLT C n, Z)} {hf} (n : ℕ) x :
    descBySkeletonLT C f hf
      (ContinuousMap.inclusion (skeletonLT C n).subset_complex x) = f n x := by
  simp [descBySkeletonLT, ContinuousMap.inclusion]

lemma descBySkeletonLT_of_mem [T2Space X] {Z} [TopologicalSpace Z]
    {f : (n : ℕ) → C(skeletonLT C n, Z)} {hf} (n : ℕ) {x} (hx : x ∈ skeletonLT C n) :
    descBySkeletonLT C f hf ⟨x, (skeletonLT C n).subset_complex hx⟩ = f n ⟨x, hx⟩ := by
  simp only [descBySkeletonLT, coe_mk]
  rw [iUnionLift_of_mem (S := fun (n : ℕ) ↦ skeletonLT C n)
    ⟨x, skeletonLT C n |>.subset_complex hx⟩ hx]



lemma skeletonLT_union_iUnion_openCell_eq_skeletonLT_succ [T2Space X] (n : ℕ) :
    ↑(skeletonLT C n) ∪ ⋃ (j : cell C n), openCell n j = skeletonLT C (n + 1) := by
  simp_rw [← iUnion_openCell_eq_skeletonLT, union_assoc, ENat.coe_lt_coe,
  ← biUnion_le (fun i ↦ ⋃ (j : cell C i), openCell i j) n, ← Nat.lt_succ_iff, Nat.succ_eq_add_one,
  ← ENat.coe_lt_coe]
  rfl

lemma isCoherentWith_skeletonLT_succ [T2Space X] (n : ℕ) :
    IsCoherentWith
      (insert (↑(skeletonLT C ↑(n + 1)) ↓∩ (skeletonLT C n : Set X))
        (range (↑(skeletonLT C ↑(n + 1)) ↓∩ 𝓔.closedCell n ·))) := by
  fapply IsCoherentWith.of_isClosed
  intro t ht
  rw [(skeletonLT C ↑(n + 1)).toComplex.isCoherentWith_closedCells.isClosed_iff]
  simp_rw [forall_mem_insert, forall_mem_range, Sigma.forall] at ht ⊢
  rcases ht with ⟨ht₁, ht₂⟩
  rw [IsClosedEmbedding.subtypeVal _ |>.isClosed_iff_image_isClosed] at ht₁
  · simp only [SetLike.coe_sort_coe, Subtype.image_preimage_coe] at ht₁
    split_ands
    · rw [IsClosedEmbedding.subtypeVal _ |>.isClosed_iff_image_isClosed]
      · simp only [SetLike.coe_sort_coe, Subtype.image_preimage_coe]
        replace ht₁ := (isClosedBase C).preimage_val.inter ht₁
        rwa [← inter_assoc, ← preimage_inter,
        inter_eq_self_of_subset_left (skeletonLT C n).base_subset] at ht₁
      · exact (isClosedBase C).preimage_val
    · simp only [SetLike.coe_sort_coe, Subcomplex.toComplex_cell, skeletonLT_I, coe_setOf,
      Subtype.forall, Nat.cast_lt]
      rintro m j hm -- rfl
      rcases (Nat.le_of_lt_succ hm).eq_or_lt' with rfl | hm
      · exact ht₂ j
      · rw [IsClosedEmbedding.subtypeVal _ |>.isClosed_iff_image_isClosed]
        · simp only [Subtype.image_preimage_coe]
          replace ht₁ := (isClosed_closedCell (i := j)).preimage_val.inter ht₁
          rwa [← inter_assoc, ← preimage_inter,
          inter_eq_self_of_subset_left (closedCell_subset_skeletonLT m j |>.trans
            <| skeletonLT_mono (Order.add_one_le_of_lt <| ENat.coe_lt_coe.mpr hm))] at ht₁
        · exact isClosed_closedCell.preimage_val
  · exact (skeletonLT C n).closed.preimage_val

lemma _root_.ENat.coe_le_succ {n : ℕ} : (n : ℕ∞) ≤ n + 1 := by simp


/-- The canonical inclusion from `skeletonLT C n ⊕ Σ (_ : cell C n), Metric.closedBall 0 1` to
`skeletonLT C (n + 1)` for finite `n`. -/
noncomputable def skeletonLTClosedCellInclusionSucc [T2Space X] (n : ℕ) :
    C(skeletonLT C n ⊕ Σ (_ : cell C n), Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      skeletonLT C (n + 1)) :=
  sum (inclusion (skeletonLT_mono ENat.coe_le_succ))
    (sigma fun j ↦ ContinuousMap.inclusion (closedCell_subset_skeletonLT n j) |>.comp <| map' n j)


-- lemma skeletonLTClosedCellInclusionSucc_inl [T2Space X] (n : ℕ) :
--     (skeletonLTClosedCellInclusionSucc C n).comp .inl =
--       .inclusion (skeletonLT_mono ENat.coe_le_succ) :=
  -- rfl

@[simp, higher_order skeletonLTClosedCellInclusionSucc_inl]
lemma skeletonLTClosedCellInclusionSucc_inl_apply [T2Space X] (n : ℕ) (x : skeletonLT C n) :
    skeletonLTClosedCellInclusionSucc C n (.inl x) =
      Set.inclusion (skeletonLT_mono ENat.coe_le_succ) x :=
  rfl

@[simp]
lemma skeletonLTClosedCellInclusionSucc_inr_apply [T2Space X] (n : ℕ)
    (x : (_ : cell C n) × Metric.closedBall 0 1) :
    skeletonLTClosedCellInclusionSucc C n (.inr x) =
      ⟨map' n x.1 x.2, closedCell_subset_skeletonLT n x.1 (map' n x.1 x.2).2⟩ :=
  rfl

-- lemma skeletonLTClosedCellInclusionSucc_inr [T2Space X] (n : ℕ) :
--     (skeletonLTClosedCellInclusionSucc C n).comp .inr =
--       sigma fun j ↦ ContinuousMap.inclusion (closedCell_subset_skeletonLT n j) |>.comp
--         <| map' n j :=
--   rfl

@[higher_order skeletonLTClosedCellInclusionSucc_inr']
lemma skeletonLTClosedCellInclusionSucc_inr_mk [T2Space X] (n : ℕ)
    (j : cell C n) (x : Metric.closedBall 0 1) :
    skeletonLTClosedCellInclusionSucc C n (.inr ⟨j, x⟩) =
      Set.inclusion (closedCell_subset_skeletonLT n j) (map' n j x) :=
  rfl


lemma skeletonLTClosedCellInclusionSucc_surjective [T2Space X] (n : ℕ) :
    Function.Surjective (skeletonLTClosedCellInclusionSucc C n) := by
  rintro ⟨x, hx⟩
  rw [← SetLike.mem_coe, ← skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ] at hx
  simp only [mem_union, mem_iUnion] at hx
  unfold skeletonLTClosedCellInclusionSucc
  rcases hx with hskel | ⟨j, ⟨x, hx', rfl⟩⟩
  · use .inl ⟨x, hskel⟩; rfl
  · use .inr ⟨j, ⟨x, hx'⟩⟩; rfl

@[simp]
lemma coinduced_map' [T2Space X] (n : ℕ) (j : cell C n) :
    coinduced (map' n j) instTopologicalSpaceSubtype = instTopologicalSpaceSubtype := by
  -- simp only [map', ContinuousMap.coe_comp, mapsTo_apply, ContinuousMap.coe_coe]
  have : CompactSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [← isCompact_iff_compactSpace]
    fapply ProperSpace.isCompact_closedBall
  rw [← IsQuotientMap.eq_coinduced]
  apply IsQuotientMap.of_surjective_continuous
  · simp [map', closedCell, surjOn_image]
  · exact ContinuousMap.continuous _

    -- simp [map n j |>.sur]

-- open isQuotientMap_skeletonLTClosedCellInclusionSucc in
/-- The canonical inclusion from `skeletonLT C n ⊕ Σ (_ : cell C n), Metric.closedBall 0 1` to
`skeletonLT C (n + 1)` is a quotient map for all finite `n`. -/
lemma isQuotientMap_skeletonLTClosedCellInclusionSucc [T2Space X] (n : ℕ) :
    IsQuotientMap (skeletonLTClosedCellInclusionSucc C n) := by
  let 𝓢 n := skeletonLT C n |>.toComplex
  have h𝓢 n := (𝓢 n).isCoherentWith_closedCells
  replace h𝓢 n := (IsCoherentWith.isQuotientMap_sigma_desc (h𝓢 n) ?surj).eq_coinduced
  case surj =>
    simp_rw [Subcomplex.toComplex_closedCell,
      sUnion_insert, sUnion_range, ← preimage_iUnion, ← preimage_union,
      iUnion_sigma]
    fapply preimage_val_eq_univ_of_subset
    simp_rw [← (skeletonLT C n).toComplex.union]
    rfl
  -- have {X Y Z : TopCat} (f : Y ≅ X) (g : Y ⟶ Z) :
  --   ⇑g ∘ (homeoOfIso f).symm = ⇑(f.inv ≫ g) := by rfl
  -- conv at h𝓢 =>
  --   enter [m]
  --   rw [← homeoOfIso (aux C m) |>.symm.coinduced_eq, coinduced_compose, this,
  --   aux_inv_desc, coprod_topology, coinduced_sup]
  --   tactic => simp_rw [coinduced_compose, ← ConcreteCategory.hom_comp]
  --   rw [coprod.inl_desc, coprod.inr_desc]
  --   tactic => simp_rw [colimit_topology, coinduced_iSup, coinduced_compose,
  --   ← ConcreteCategory.hom_comp]
  --   conv in colimit.ι _ _ =>
  --     change colimit.ι _ (Discrete.mk i.as)
  --     rw [← Sigma.ι.eq_def]
  --   tactic => simp_rw [Sigma.ι_desc, Discrete.functor_obj_eq_as]
  -- induction n using Nat.case_strong_induction_on with
  -- | hz =>
  fconstructor
  · exact skeletonLTClosedCellInclusionSucc_surjective C n
  · have discrete_iSup {α β : Type u} [SupSet β] {f : Discrete α → β} :
        (⨆ (a : Discrete α), f a) = ⨆ (a' : α), f ⟨a'⟩ := by
      apply discreteEquiv.iSup_congr; simp
    unfold instTopologicalSpaceSum instTopologicalSpaceSigma
    conv =>
      args
      · rw [h𝓢]
      · arg 2; args
        · rw [h𝓢]
        · simp only
    simp_rw [instTopologicalSpaceSigma, coinduced_sup, coinduced_iSup, coinduced_compose,
    -- ← coe_inr,
    -- ← coe_sigmaMk,
    -- ← ContinuousMap.coe_comp, ← ContinuousMap.comp_assoc,
    skeletonLTClosedCellInclusionSucc_inr', sigma, coe_mk, Function.comp_def (g := Sigma.mk _),
    -- ← coe_comp, Sigma.ι_desc, ConcreteCategory.hom_ofHom,
    ← Function.comp_assoc,
    skeletonLTClosedCellInclusionSucc_inl, iSup_subtype, iSup_insert, iSup_range, iSup_sigma,
    sup_assoc, iSup_sup]
    congr! 1
    · simp_rw [subtypeVal, coe_mk,
      ← coinduced_inclusion_eq_coinduced_val (Subcomplex.base_subset _),
      ← coinduced_inclPreimageVal (Subcomplex.base_subset _), coinduced_compose]
      congr!
    · conv =>
        conv =>
          enter [2, 1, m]
          conv =>
            left; change ⨆ (j : (skeletonLT C n).I m), _
        args <;> enter [1, m]
        focus change ⨆ (j : (skeletonLT C ↑(n + 1)).I m), _
        all_goals
          simp only [iSup_subtype, skeletonLT_I, SetLike.coe_sort_coe, mem_setOf_eq,
          ENat.coe_lt_coe]
          rw [iSup_comm]
          rfl
      conv_lhs =>
        enter [1, m]
        tactic =>
          simp_rw [← Nat.le_iff_lt_add_one, le_iff_lt_or_eq, iSup_or]
      simp_rw [iSup_sup_eq, iSup_iSup_eq_left, iSup_const]
      congr! 6 with m hm j j
      focus symm
      all_goals
        simp_rw [subtypeVal, coe_mk]
        rw [← coinduced_inclPreimageVal, coinduced_compose]
      · rw [← coinduced_inclusion_eq_coinduced_val]
        · congr!
        · exact (skeletonLT C ↑(n + 1)).toComplex.closedCell_subset_complex m
            ⟨j, by simpa [skeletonLT_I] using trans (ENat.coe_lt_coe.mpr hm) ENat.coe_le_succ⟩
      · exact (skeletonLT C n).toComplex.closedCell_subset_complex m
          ⟨j, by simpa [skeletonLT_I] using hm⟩
      · conv_rhs =>
          rw [← coinduced_compose]
          simp only [coinduced_map']
        congr!
      all_goals
        exact (skeletonLT C ↑(n + 1)).toComplex.closedCell_subset_complex n
          ⟨j, by simp [skeletonLT_I, -Nat.cast_add]⟩

variable {C} in
/-- A point that is known to be in `Metric.closedBall 0 1` that is also in the preimage of
a cell frontier is in `Metric.sphere 0 1`. -/
lemma map_mem_cellFrontier_iff {n} {j : cell C n} {x} (hx : x ∈ Metric.closedBall 0 1) :
    map n j x ∈ cellFrontier n j ↔ x ∈ Metric.sphere 0 1 := by
  have : x ∈ Metric.ball 0 1 → (map n j x) ∉ cellFrontier n j := by
    intro hx hx'
    have : (map n j x) ∈ openCell n j := mem_image_of_mem _ hx
    exact (disjoint_openCell_cellFrontier _ _).notMem_of_mem_right hx' this
  constructor
  · rintro ⟨y, hy, h⟩
    by_contra hx'
    replace hx : ‖x - 0‖ < 1 := by simpa using lt_of_le_of_ne hx hx'
    rw [← mem_ball_iff_norm] at hx
    fapply this hx
    rw [← h]; exact mem_image_of_mem _ hy
  · intro hx; exact ⟨x, hx, rfl⟩

variable {C} in
@[simp]
lemma inter_closedCell_subset_cellFrontier_left {n} {j₁ j₂ : cell C n} (hj : j₁ ≠ j₂) :
    closedCell n j₁ ∩ closedCell n j₂ ⊆ cellFrontier n j₁ := by
  have : Sigma.mk n j₁ ≠ Sigma.mk n j₂ := by simp [hj]
  simp [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left,
  union_inter_distrib_right, (disjoint_openCell_cellFrontier j₂ j₁).inter_eq,
  (disjoint_openCell_of_ne this).inter_eq]

variable {C} in
/-- If for some `x, y`, `x ≠ y` and `x, y ∈ Metric.closedBall 0 1` we have `map n j x = map n k y`,
then `x` and `y` are both `∈ Metric.sphere 0 1`. -/
lemma mem_sphere_of_map_eq {n} {j k : cell C n} {x y} (hxy : x ≠ y)
    (hx : x ∈ Metric.closedBall 0 1) (hy : y ∈ Metric.closedBall 0 1)
    (h : map n j x = map n k y) : x ∈ Metric.sphere 0 1 ∧ y ∈ Metric.sphere 0 1 := by
  rcases em (j = k) with rfl | hjk
  · by_contra h'
    rw [not_and_or] at h'
    wlog hx' : x ∉ Metric.sphere 0 1 generalizing x y
    · rw [Classical.not_not] at hx'
      have h'' := h'.neg_resolve_left hx'
      exact this hxy.symm hy hx h.symm h'.symm h''
    · rw [← Metric.ball_union_sphere] at hx hy
      replace hx := Or.resolve_right hx hx'
      rcases hy with hy | hy
      · rw [← source_eq n j] at hx hy
        exact hxy <| (map n j).injOn hx hy h
      · replace hx : (map n j) x ∈ openCell n j := mem_image_of_mem _ hx
        replace hy : (map n j) y ∈ cellFrontier n j := mem_image_of_mem _ hy
        rw [h] at hx
        exact (disjoint_openCell_cellFrontier _ _).notMem_of_mem_right hy hx
  · push_neg at hjk
    split_ands
    · have := inter_closedCell_subset_cellFrontier_left hjk
        ⟨mem_image_of_mem _ hx, h ▸ mem_image_of_mem _ hy⟩
      rwa [map_mem_cellFrontier_iff hx] at this
    · have := inter_closedCell_subset_cellFrontier_left hjk.symm
        ⟨mem_image_of_mem _ hy, h ▸ mem_image_of_mem _ hx⟩
      rwa [map_mem_cellFrontier_iff hy] at this

section

variable [T2Space X] (n : ℕ) {Z} [TopologicalSpace Z]
    (sk : C(skeletonLT C n, Z)) (cells : (j : cell C n) → C(Metric.closedBall 0 1, Z))
    (coherence_sk : ∀ (j : cell C n) (x : Metric.sphere 0 1),
      sk ⟨(skeletonLT C ↑(n + 1)).toComplex.map n
            ⟨j, by simp [-Nat.cast_add, skeletonLT_I, n.lt_succ_self]⟩ x,
          cellFrontier_subset_skeletonLT n j <| mem_image_of_mem _ x.2⟩ =
        cells j (Set.inclusion Metric.sphere_subset_closedBall x))
    (coherence_cells : ∀ {j k : cell C n} {x y : Metric.sphere 0 1}, map n j x.1 = map n k y.1 →
      cells j (Set.inclusion Metric.sphere_subset_closedBall x) =
        cells k (Set.inclusion Metric.sphere_subset_closedBall y))

attribute [local simp] Homeomorph.ulift Equiv.ulift ContinuousMap.inclusion in
noncomputable def skeletonLT.succ_desc : C(skeletonLT C (n + 1), Z) :=
  isQuotientMap_skeletonLTClosedCellInclusionSucc C n |>.lift (.sum sk <| .sigma cells) <| by
    simp only [Subcomplex.toComplex_map, Subtype.forall] at coherence_sk coherence_cells
    rintro (x | ⟨j, x, hx⟩) (y | ⟨k, y, hy⟩) h
    · simp at h; simp [h]
    rotate_right
    · rcases em (x = y) with rfl | hxy
      · rcases em (j = k) with rfl | hjk
        · simp
        · have hx' := inter_closedCell_subset_cellFrontier_left hjk
            ⟨mem_image_of_mem _ hx, by simp at h; exact h ▸ mem_image_of_mem _ hx⟩
          rw [map_mem_cellFrontier_iff hx] at hx'
          simp at h
          simpa using coherence_cells _ hx' _ hx' h
      · obtain ⟨hx, hy⟩ := mem_sphere_of_map_eq hxy hx hy <| by simpa using h
        simp at h
        simpa using coherence_cells _ hx _ hy h
    swap; focus symm at h
    all_goals
      simp [← exists_eq_subtype_mk_iff] at h
      obtain ⟨hx, rfl⟩ := h
      have hy' := skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier
        (ENat.coe_le_coe.mpr <| le_refl n) |>.subset ⟨hx, mem_image_of_mem _ ‹_›⟩ |>.2
      rw [map_mem_cellFrontier_iff ‹_›] at hy'
      specialize coherence_sk ‹_› _ hy'
      simp [coherence_sk] at hx ⊢

#check IsQuotientMap.liftEquiv_apply

variable {n sk cells coherence_sk coherence_cells}

@[simp, higher_order skeletonLT.succ_desc_sk]
lemma skeletonLT.succ_desc_sk_apply
    (_h : (skeletonLT C ↑n : Set X) ⊆ skeletonLT C (↑n + 1) := skeletonLT_mono ENat.coe_le_succ)
    (x : skeletonLT C n) :
    (skeletonLT.succ_desc C n sk cells coherence_sk coherence_cells)
      (ContinuousMap.inclusion _h x) = sk x := by
  unfold succ_desc
  rw [ContinuousMap.coe_inclusion, ← skeletonLTClosedCellInclusionSucc_inl, Function.comp_apply]
  simp [↓isQuotientMap_skeletonLTClosedCellInclusionSucc C n |>.lift_comp_apply]

@[simp, higher_order skeletonLT.succ_desc_cell]
lemma skeletonLT.succ_desc_cell_apply (j : cell C n)
    (_h : closedCell n j ⊆ skeletonLT C (↑n + 1) := closedCell_subset_skeletonLT n j) x :
    (skeletonLT.succ_desc C n sk cells coherence_sk coherence_cells)
      (ContinuousMap.inclusion _h (map' n j x)) = cells j x := by
  unfold succ_desc
  rw [ContinuousMap.coe_inclusion, ← skeletonLTClosedCellInclusionSucc_inr_mk]
  simp


end

noncomputable def toRelativeCWComplex [T2Space X] :
    RelativeCWComplex (ofHom <| inclusion base_subset_complex : of D ⟶ of C) where
  F := WithTop.functor ℕ ⋙ skeletonLT.asFunctor C
  isoBot := isoOfHomeo <| Subcomplex.homeoExt (skeletonLT_zero_eq_base (C := C))
  isWellOrderContinuous := inferInstance
  incl := { app n := ofHom <| inclusion <| skeletonLT C n |>.subset_complex }
  isColimit :=
  { desc s := ofHom <| descBySkeletonLT C (Hom.hom <| s.ι.app ·) fun n x ↦ by
      have := s.ι.naturality (homOfLE n.le_succ)
      change (ofHom (.inclusion _) ≫ s.ι.app (n + 1)) x = s.ι.app n x
      simp at this; simp [this]
    fac s n := by ext x; simp [ContinuousMap.inclusion, descBySkeletonLT]
    uniq s m hm := by
      ext ⟨x, hx⟩
      rw [← 𝓔.skeletonLT_top, SetLike.mem_coe, mem_skeletonLT_iff] at hx
      simp_rw [TopCat.ext_iff] at hm
      rcases hx with hx | ⟨n, -, j, hx⟩
      · specialize hm 0 ⟨x, by simpa [← 𝓔.skeletonLT_zero_eq_base] using hx⟩
        rw [ConcreteCategory.hom_ofHom, descBySkeletonLT_of_mem]
        simpa [ContinuousMap.inclusion, Hom.hom] using hm
      · specialize hm (n + 1) ⟨x, openCell_subset_skeletonLT n j hx⟩
        rw [ConcreteCategory.hom_ofHom, descBySkeletonLT_of_mem]
        simpa [ContinuousMap.inclusion, Hom.hom] using hm }
  fac := by ext x; simp [ContinuousMap.inclusion]
  attachCells n _ :=
    let m := Limits.Sigma.map (fun (_ : cell C n) ↦ diskBoundaryInclusion n)
    have : Mono m := by
      unfold m
      rw [TopCat.mono_iff_injective, ← (homeoOfIso <| sigmaIsoSigma _).symm.injective_comp,
      ← (homeoOfIso <| sigmaIsoSigma _).comp_injective]
      rintro ⟨j, x⟩ ⟨k, y⟩ h
      simp only [homeoOfIso, Equiv.coe_fn_mk, Homeomorph.coe_toEquiv,
        Homeomorph.homeomorph_mk_coe_symm, Equiv.coe_fn_symm_mk, Function.comp_apply] at h
      rw [sigmaIsoSigma_inv_apply, sigmaIsoSigma_inv_apply] at h
      simp [← ConcreteCategory.comp_apply, - TopCat.hom_comp, - ContinuousMap.comp_apply,
      -TopCat.comp_app, - TopCat.coe_comp] at h
      simpa [(TopCat.mono_iff_injective _).mp inferInstance |>.eq_iff] using h
    have : (forget TopCat).PreservesMonomorphisms := inferInstance
    have : Mono (forget TopCat |>.map m) := this.preserves m
  { ι := cell C n
    π _ := ()
    cofan₁ := _
    cofan₂ := _
    isColimit₁ := coproductIsCoproduct (fun _ ↦ ∂𝔻 n)
    isColimit₂ := coproductIsCoproduct (fun _ ↦ 𝔻 n)
    m
    hm j := by simp [m]
    g₁ := Sigma.desc fun j ↦ ofHom <| .comp
      (.mapsTo (↑(map n j)) (Metric.sphere 0 1) (skeletonLT C ↑n)
        (fun ⦃x⦄ hx ↦ cellFrontier_subset_skeletonLT n j <| by
          simpa [cellFrontier, -mem_sphere_iff_norm, -Metric.mem_sphere] using ⟨x, hx, rfl⟩)
        (ContinuousOn.mono (continuousOn n j) Metric.sphere_subset_closedBall))
      (toContinuousMap Homeomorph.ulift)
    g₂ := Sigma.desc fun j ↦ ofHom <| .comp
      (.inclusion (closedCell_subset_skeletonLT n j))
      (map' n j |>.comp <| toContinuousMap Homeomorph.ulift)
    isPushout :=
    { w := by
        apply Limits.Sigma.hom_ext
        intro j; ext x
        simp [ContinuousMap.inclusion, m, MapsTo.restrict, Subtype.map] --, ↓Sigma.ι_desc]
        congr
      isColimit' := by
        constructor
        have diskBoundaryInclusion_eq x : diskBoundaryInclusion n ⟨x⟩ =
              (toContinuousMap Homeomorph.ulift.symm : C(_, disk.{u} _))
                (Set.inclusion Metric.sphere_subset_closedBall x) := by
          simp [Homeomorph.ulift, Equiv.ulift, diskBoundaryInclusion, disk]
        fapply PushoutCocone.IsColimit.mk
        · rintro ⟨pt, ι⟩
          haveI ι_l := by simpa [RelativeCWComplex.basicCell, Sigma.hom_ext_iff, Function.comp_def,
            ← Sigma.ι.eq_def, m] using ι.naturality WalkingSpan.Hom.fst
          haveI ι_r := by simpa [RelativeCWComplex.basicCell, Sigma.hom_ext_iff, Function.comp_def,
            ← Sigma.ι.eq_def, m] using ι.naturality WalkingSpan.Hom.snd
          fapply ofHom
          fapply skeletonLT.succ_desc
          · exact ConcreteCategory.hom <| ι.app WalkingSpan.left
          · exact (fun j ↦ ConcreteCategory.hom (Sigma.ι _ j ≫ ι.app WalkingSpan.right) |>.comp
              (toContinuousMap Homeomorph.ulift.symm)) -- .comp (toContinuousMap Homeomorph.ulift))
          · intro j x
            simp only [Functor.const_obj_obj]
            rw [ContinuousMap.comp_apply, ← diskBoundaryInclusion_eq,
            ← ConcreteCategory.comp_apply]
            -- erw [← ConcreteCategory.comp_apply]
            simp [ι_r, ← ι_l, ContinuousMap.mapsTo, MapsTo.restrict, Homeomorph.ulift, Equiv.ulift]
            rfl
          · intro j k x y h
            simp_rw [Functor.const_obj_obj, ContinuousMap.comp_apply, ← diskBoundaryInclusion_eq,
            ← ConcreteCategory.comp_apply]
            simp [ι_r, ← ι_l, ContinuousMap.mapsTo, MapsTo.restrict, Homeomorph.ulift, Equiv.ulift,
            Subtype.map, h]
        · rintro ⟨pt, ι⟩
          ext (x : skeletonLT C n)
          simp_rw [ConcreteCategory.comp_apply, Functor.comp_map, Functor.comp_obj,
          skeletonLT.asFunctor_map, skeletonLT.asFunctor_obj, WithTop.functor_obj, hom_ofHom]
          erw [skeletonLT.succ_desc_sk_apply C]
          rfl
        · rintro ⟨pt, ι⟩
          fapply Sigma.hom_ext; intro j
          ext x
          rw [Sigma.ι_desc_assoc, ← ContinuousMap.comp_assoc,
          ← sigma_comp_mk (.comp (.inclusion _) <| map' n ·) j]
          simp only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom, sigma_comp_mk]
          erw [skeletonLT.succ_desc_cell_apply C, ContinuousMap.comp_apply]
        · have eq_ofHom_iff {X Y : TopCat} (f : X ⟶ Y) (g : C(X, Y)) :
              f = ofHom g ↔ ConcreteCategory.hom f = g := by
            constructor <;> {rintro rfl; rfl}
          rintro ⟨pt, ι⟩ (m : of (skeletonLT C ↑(n + 1)) ⟶ pt) hm₁ hm₂
          change of (skeletonLT C (n + 1)) ⟶ pt at m
          unfold skeletonLT.succ_desc
          rw [eq_ofHom_iff, (isQuotientMap_skeletonLTClosedCellInclusionSucc C n).liftEquiv_apply']
          erw [← (IsQuotientMap.liftEquiv _).symm_apply_eq]
          ext (x | ⟨j, x⟩)
          · simp [TopCat.ext_iff, Hom.hom, ContinuousMap.inclusion, -Subtype.forall,
            PushoutCocone.inl] at hm₁
            simp [← hm₁] --; rfl
          · simp [TopCat.ext_iff, Sigma.hom_ext_iff, ↓Sigma.ι_desc_assoc, Hom.hom,
            ContinuousMap.inclusion, -Subtype.forall, PushoutCocone.inr] at hm₂
            simp [← hm₂, MapsTo.restrict, Subtype.map] --; rfl
    }
  }

end Topology.RelCWComplex
