
open Classical Function.Injective in
/-- A closed embedding from some space `Y` onto `X` whose range includes `C` induces a
`RelCWComplex` on `Y`. -/
@[simps]
noncomputable def pullback {Y : Type u} [TopologicalSpace Y]
    (f : Y → X) (hf : IsClosedEmbedding f) (hC : univ.SurjOn f C) :
    RelCWComplex (f ⁻¹' C) (f ⁻¹' D) where
  cell := 𝓔.cell
  map n j :=
    if C₀ : C = ∅ then elim C₀ j else
      have Y₀ := hC₀ C₀
      (𝓔.map n j |>.trans (hf.injective.toPartialEquiv).symm)
  source_eq n j := if C₀ : C = ∅ then elim0 C₀ j else by
    simpa [C₀, source_eq, ← openCell.eq_def, ← image_subset_iff] using
      openCell_subset_complex n j |>.trans hC
  continuousOn n j := if C₀ : C = ∅ then elim0 C₀ j else by
    · have Y₀ : Nonempty Y := hC₀ C₀
      simp only [C₀, ↓reduceDIte, PartialEquiv.coe_trans, toPartialEquiv_symm_apply]
      refine ContinuousOn.comp ?_ (𝓔.continuousOn n j)
        (Set.mapsTo_iff_image_subset.mpr <| closedCell_subset_complex n j)
      rw [continuousOn_iff']
      cases hf'
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨t, ht, ?_⟩
      ext x
      simp only [mem_inter_iff, mem_preimage, and_congr_left_iff]
      intro hx
      rw [Function.invFunOn_eq (hx' x hx)]
  continuousOn_symm n j := if C₀ : C = ∅ then elim0 C₀ j else by
    · have Y₀ : Nonempty Y := hC₀ C₀
      simp only [C₀, ↓reduceDIte]
      conv =>
        arg 2
        rw [← univ_inter (PartialEquiv.target _)]
      simpa [PartialEquiv.subtype] using
        ContinuousOn.comp_inter (𝓔.continuousOn_symm n j) (show ContinuousOn f univ by
          rw [continuousOn_univ]; exact hf.continuous)
  pairwiseDisjoint' := by
    rintro ⟨n, i⟩ - ⟨m, j⟩ - h
    if C₀ : C = ∅ then exact elim0 C₀ j else
    have Y₀ : Nonempty Y := hC₀ C₀
    have := 𝓔.pairwiseDisjoint trivial trivial h
    rw [Function.onFun] at this
    simpa [C₀, ↓reduceDIte, -Function.comp_apply, image_comp, ← openCell.eq_def, Function.onFun]
      using this.image (Function.invFunOn_injOn_image f univ)
      (by simpa using openCell_subset_complex n i |>.trans hC)
      (by simpa using openCell_subset_complex m j |>.trans hC)
  disjointBase' n j := if C₀ : C = ∅ then elim0 C₀ j else by
    have Y₀ : Nonempty Y := hC₀ C₀
    have := 𝓔.disjointBase' n j
    replace this := this.preimage f
    refine Disjoint.mono_left ?_ (by simpa [C₀, ↓reduceDIte] using this)
    simp_rw [Set.le_eq_subset, ← Set.image_subset_iff]
    intro x hx
    simp only [C₀, ↓reduceDIte, PartialEquiv.coe_trans, PartialEquiv.subtype_symm_apply,
      image_comp, ← openCell.eq_def, mem_image, exists_exists_and_eq_and] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    simpa [Function.invFunOn_eq (hx' x <| openCell_subset_complex n j hx), -Metric.mem_ball]
      using hx
  mapsTo n j := if C₀ : C = ∅ then elim0 C₀ j else by
    have Y₀ : Nonempty Y := hC₀ C₀
    obtain ⟨I, hI⟩ := 𝓔.mapsTo n j
    use I
    simp only [C₀, ↓reduceDIte, PartialEquiv.coe_trans, toPartialEquiv_symm_apply,
      Function.comp_apply]
    refine MapsTo.comp ?_ hI
    rintro x (hxD | hx_cell)
    · simpa [Function.invFunOn_eq (hx' x <| base_subset_complex hxD), -Metric.mem_ball]
        using Or.inl hxD
    · obtain ⟨i, hi, j, hj, z, hz, rfl⟩ := by simpa using hx_cell
      simpa using Or.inr ⟨i, hi, j, hj, z, hz, rfl⟩
  closed' A hA
  | ⟨hA_cell, hAD⟩ => by
    if C₀ : C = ∅ then simp_all else
    have Y₀ : Nonempty Y := hC₀ C₀
    simp only [C₀, ↓reduceDIte, PartialEquiv.coe_trans, toPartialEquiv_symm_apply,
      image_comp, ← closedCell.eq_def] at hA_cell
    rw [hf.isClosed_iff_image_isClosed]
    fapply 𝓔.closed'
    · simp [hA]
    · split_ands
      · peel hA_cell with n j hA_cell
        rw [hf.isClosed_iff_image_isClosed] at hA_cell
        simpa [image_inter hf.injective,
        hC.image_invFunOn_image_of_subset <| closedCell_subset_complex n j] using hA_cell
      · rw [hf.isClosed_iff_image_isClosed] at hAD
        simpa [image_inter hf.injective, hC.image_preimage <| base_subset_complex] using hAD
  isClosedBase := hf.isClosed_preimage _ 𝓔.isClosedBase
  union' := by
    if C₀ : C = ∅ then
      simpa [C₀, base_empty_of_complex_empty C C₀] using (fun n j ↦ elim0 C₀ j)
    else
      have Y₀ : Nonempty Y := hC₀ C₀
      apply image_injective.mpr hf.injective
      simp only [C₀, ↓reduceDIte, PartialEquiv.coe_trans, toPartialEquiv_symm_apply,
        image_comp]
      simp_rw [← image_iUnion, image_union, hC.image_preimage <| base_subset_complex,
      hC.image_preimage <| subset_refl C]
      rw [hC.image_invFunOn_image_of_subset]
      · exact 𝓔.union'
      · simp [← 𝓔.union']
where
  hf' := hf.eq_induced
  hx' : ∀ x ∈ C, ∃ y ∈ univ, f y = x :=
    fun x hx ↦ ⟨(hC.subset_range hx).choose, mem_univ _, (hC.subset_range hx).choose_spec⟩
  hC₀ (C₀ : ¬C = ∅) : Nonempty Y := ⟨by
    rw [eq_empty_iff_forall_notMem] at C₀
    push_neg at C₀
    exact (hC C₀.choose_spec).choose⟩
  elim {α : Type _} (C₀ : C = ∅) {n} (j : cell C n) : α :=
    (cells_empty_of_complex_empty C₀ n).elim j
  elim0 {α : Prop} (C₀ : C = ∅) {n} (j : cell C n) : α :=
    (cells_empty_of_complex_empty C₀ n).elim j

@[simp]
lemma pullback_map_nonempty {Y : Type u} [TopologicalSpace Y] (C₀ : C.Nonempty)
    (f : Y → X) (hf : IsClosedEmbedding f) (hC : univ.SurjOn f C) (n : ℕ) (j : cell C n) :
    have : Nonempty Y := ⟨hC (C₀.choose_spec) |>.choose⟩
    (pullback C f hf hC).map n j = (𝓔.map n j).trans (hf.injective.toPartialEquiv).symm := by
  intro Y₀
  rw [nonempty_iff_ne_empty] at C₀
  simp [C₀]

@[simp]
lemma pullback_openCell {Y : Type u} [TopologicalSpace Y]
    {f : Y → X} {hf : IsClosedEmbedding f} {hC : univ.SurjOn f C} (n : ℕ) (j : cell C n) :
    (pullback C f hf hC).openCell n j = f ⁻¹' (openCell n j) := by
  have C₀ : C ≠ ∅ := complex_nonempty_of_cell j
  rw [← nonempty_iff_ne_empty] at C₀
  have Y₀ : Nonempty Y := ⟨hC (C₀.choose_spec) |>.choose⟩
  rw [nonempty_iff_ne_empty] at C₀
  unfold openCell
  simp only [pullback_map, C₀, ↓reduceDIte, PartialEquiv.coe_trans,
    Function.Injective.toPartialEquiv_symm_apply, Function.comp_apply]
  simp_rw [← Function.comp_def, image_comp, ← openCell.eq_def]
  apply hf.injective.image_injective
  rw [hC.image_invFunOn_image_of_subset <| openCell_subset_complex n j,
  hC.image_preimage <| openCell_subset_complex n j]

@[simp]
lemma pullback_closedCell {Y : Type u} [TopologicalSpace Y]
    {f : Y → X} {hf : IsClosedEmbedding f} {hC : univ.SurjOn f C} (n : ℕ) (j : cell C n) :
    (pullback C f hf hC).closedCell n j = f ⁻¹' (closedCell n j) := by
  have C₀ : C ≠ ∅ := complex_nonempty_of_cell j
  rw [← nonempty_iff_ne_empty] at C₀
  have Y₀ : Nonempty Y := ⟨hC (C₀.choose_spec) |>.choose⟩
  rw [nonempty_iff_ne_empty] at C₀
  unfold closedCell
  simp only [pullback_map, C₀, ↓reduceDIte, PartialEquiv.coe_trans,
    Function.Injective.toPartialEquiv_symm_apply, Function.comp_apply]
  simp_rw [← Function.comp_def, image_comp, ← closedCell.eq_def]
  apply hf.injective.image_injective
  rw [hC.image_invFunOn_image_of_subset <| closedCell_subset_complex n j,
  hC.image_preimage <| closedCell_subset_complex n j]

@[simp]
lemma pullback_cellFrontier {Y : Type u} [TopologicalSpace Y]
    {f : Y → X} {hf : IsClosedEmbedding f} {hC : univ.SurjOn f C} (n : ℕ) (j : cell C n) :
    (pullback C f hf hC).cellFrontier n j = f ⁻¹' (cellFrontier n j) := by
  have C₀ : C ≠ ∅ := complex_nonempty_of_cell j
  rw [← nonempty_iff_ne_empty] at C₀
  have Y₀ : Nonempty Y := ⟨hC (C₀.choose_spec) |>.choose⟩
  rw [nonempty_iff_ne_empty] at C₀
  unfold cellFrontier
  simp only [pullback_map, C₀, ↓reduceDIte, PartialEquiv.coe_trans,
    Function.Injective.toPartialEquiv_symm_apply, Function.comp_apply]
  simp_rw [← Function.comp_def, image_comp, ← cellFrontier.eq_def]
  apply hf.injective.image_injective
  rw [hC.image_invFunOn_image_of_subset <| cellFrontier_subset_complex n j,
  hC.image_preimage <| cellFrontier_subset_complex n j]

lemma pullback_skeletonLT [T2Space X] {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    {f : Y → X} {hf : IsClosedEmbedding f} {hC : univ.SurjOn f C} (n : ℕ) :
    (pullback C f hf hC).skeletonLT _ n = f ⁻¹' (skeletonLT C n) := by
  simp_rw [RelCWComplex.skeletonLT, preimage_union, preimage_iUnion, pullback_closedCell]
  rfl

/-- A `RelCWComplex C D` on `X` can be pulled back to a `RelCWComplex` on `C` itself. -/
@[simps!]
noncomputable instance shrinkwrap [T2Space X] : @RelCWComplex C inferInstance (C ↓∩ C) (C ↓∩ D) :=
  pullback C _ (IsClosedEmbedding.subtypeVal <| isClosed (C := C)) (by simp [SurjOn])

lemma shrinkwrap_openCell [T2Space X] {n : ℕ} (j : cell C n) :
    (shrinkwrap C).openCell n j = C ↓∩ openCell n j := by
  simp_rw [pullback_openCell]

lemma shrinkwrap_closedCell [T2Space X] {n : ℕ} (j : cell C n) :
    (shrinkwrap C).closedCell n j = C ↓∩ closedCell n j := by
  simp_rw [pullback_closedCell]

lemma shrinkwrap_cellFrontier [T2Space X] {n : ℕ} (j : cell C n) :
    (shrinkwrap C).cellFrontier n j = C ↓∩ cellFrontier n j := by
  simp_rw [pullback_cellFrontier]

lemma shrinkwrap_skeletonLT [T2Space X] {n : ℕ} :
    (shrinkwrap C).skeletonLT _ n = C ↓∩ skeletonLT C n := by
  simp_rw [pullback_skeletonLT]
