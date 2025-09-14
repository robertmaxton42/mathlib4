/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Category.TopCat.Limits.Products

import Mathlib.Tactic.ENatToNat

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

namespace Topology
variable {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
namespace RelCWComplex
variable [𝓔 : RelCWComplex C D]

@[simp]
lemma coinduced_map' [T2Space X] (n : ℕ) (j : cell C n) :
    coinduced (map' n j) instTopologicalSpaceSubtype = instTopologicalSpaceSubtype := by
  have : CompactSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [← isCompact_iff_compactSpace]
    fapply ProperSpace.isCompact_closedBall
  rw [← IsQuotientMap.eq_coinduced]
  apply IsQuotientMap.of_surjective_continuous
  · simp [map', closedCell, surjOn_image]
  · exact ContinuousMap.continuous _

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

/-- The canonical inclusion from `skeletonLT C n ⊕ Σ (_ : cell C n), Metric.closedBall 0 1` to
`skeletonLT C (n + 1)` for finite `n`. -/
noncomputable def skeletonLTClosedCellInclusionSucc [T2Space X] (n : ℕ) :
    C(skeletonLT C n ⊕ Σ (_ : cell C n), Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      skeletonLT C (n + 1)) :=
  sum (inclusion (skeletonLT_mono ENat.coe_le_succ))
    (sigma fun j ↦ ContinuousMap.inclusion (closedCell_subset_skeletonLT n j) |>.comp <| map' n j)


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

@[higher_order skeletonLTClosedCellInclusionSucc_inr]
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

/-- The canonical inclusion from `skeletonLT C n ⊕ Σ (_ : cell C n), Metric.closedBall 0 1` to
`skeletonLT C (n + 1)` is a quotient map for all finite `n`. -/
lemma isQuotientMap_skeletonLTClosedCellInclusionSucc [T2Space X] (n : ℕ) :
    IsQuotientMap (skeletonLTClosedCellInclusionSucc C n) := by
  fconstructor
  · exact skeletonLTClosedCellInclusionSucc_surjective C n
  · conv_lhs => rw [h𝓢 n]
    unfold instTopologicalSpaceSum instTopologicalSpaceSigma
    -- simp [sigma]
    simp_rw [coinduced_sup, coinduced_iSup, coinduced_compose,
    skeletonLTClosedCellInclusionSucc_inr, sigma, coe_mk, Function.comp_def (g := Sigma.mk _),
    skeletonLTClosedCellInclusionSucc_inl, iSup_subtype, iSup_insert, iSup_range]
    congr!
    · simp_rw [← Homeomorph.Set.preimageVal (skeletonLT_mono ENat.coe_le_succ) |>.coinduced_eq,
      coinduced_compose]
      congr!
    · simp_rw [← Homeomorph.Set.preimageVal (closedCell_subset_skeletonLT _ _) |>.coinduced_eq]
      rw [← coinduced_compose, coinduced_compose]
      congr!
      simp [coinduced_map']
where
  h𝓢 n := by
    refine IsCoherentWith.isQuotientMap_sigma_desc (skeletonLT_succ_isCoherentWith C n) ?surj
      |>.eq_coinduced
    simp_rw [sUnion_insert, sUnion_range, ← preimage_iUnion, ← preimage_union]
    fapply preimage_val_eq_univ_of_subset
    rw [skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ]; rfl

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
/-- Descend from the `(n + 1)`-skeleton, given a continuous map from the `n`-skeleton and a map
from `𝔻 n` for each `cell C n`. -/
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
  isoBot := isoOfHomeo <| Homeomorph.setCongr (skeletonLT_zero_eq_base (C := C))
  isWellOrderContinuous := inferInstance
  incl := { app n := ofHom <| inclusion <| skeletonLT C n |>.subset_complex }
  isColimit :=
  { desc s := ofHom <| descBySkeletonLT C (Hom.hom <| s.ι.app ·) fun n x ↦ by
      have := s.ι.naturality (homOfLE n.le_succ)
      change (ofHom (.inclusion _) ≫ s.ι.app (n + 1)) x = s.ι.app n x
      simp at this; simp [this]
    fac s n := by ext x; simp [ContinuousMap.inclusion]
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
  fac := by
    ext ⟨x, hx⟩
    simpa [ContinuousMap.inclusion, Homeomorph.setCongr] using
      Subtype.ext_iff.mp <| Equiv.setCongr_symm_apply _ ⟨x, hx⟩
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
        simp [ContinuousMap.inclusion, m, MapsTo.restrict, Subtype.map]
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
              (toContinuousMap Homeomorph.ulift.symm))
          · intro j x
            simp only [Functor.const_obj_obj]
            rw [ContinuousMap.comp_apply, ← diskBoundaryInclusion_eq,
            ← ConcreteCategory.comp_apply]
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

#min_imports
