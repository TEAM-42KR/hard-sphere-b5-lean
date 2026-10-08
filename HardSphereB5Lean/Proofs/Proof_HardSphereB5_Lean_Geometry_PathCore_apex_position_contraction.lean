import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_apex_anchor
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_tetrahedron_metric
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma APC_triangle_lapex (hc : IsPathConfig c X Y s) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Lapex c i j k + Lapex c j i k + Lapex c k i j = 2 := by
  have hD : Deltaf c i j k ≠ 0 := ne_of_gt ((tetrahedron_metric hc).2.2.2.1 i j k hij hik hjk)
  have hji : q c j i = q c i j := by simp [q, dist_comm]
  have hki : q c k i = q c i k := by simp [q, dist_comm]
  have hkj : q c k j = q c j k := by simp [q, dist_comm]
  have hD2 : Deltaf c j i k = Deltaf c i j k := by
    unfold Deltaf DeltaT
    rw [hji]
    ring
  have hD3 : Deltaf c k i j = Deltaf c i j k := by
    unfold Deltaf DeltaT
    rw [hki, hkj]
    ring
  unfold Lapex
  rw [hD2, hD3, hji, hki, hkj]
  field_simp
  unfold Deltaf DeltaT
  ring

private lemma APC_face_lapex (hc : IsPathConfig c X Y s) (l : Fin 4) :
    (∑ i : Fin 4, if l ≠ i then Lapex c i (oth1 i l) (oth2 i l) else 0) = 2 := by
  fin_cases l
  · simpa [Fin.sum_univ_succ, oth1, oth2, add_assoc] using
      APC_triangle_lapex hc 1 2 3 (by decide) (by decide) (by decide)
  · simpa [Fin.sum_univ_succ, oth1, oth2, add_assoc] using
      APC_triangle_lapex hc 0 2 3 (by decide) (by decide) (by decide)
  · simpa [Fin.sum_univ_succ, oth1, oth2, add_assoc] using
      APC_triangle_lapex hc 0 1 3 (by decide) (by decide) (by decide)
  · simpa [Fin.sum_univ_succ, oth1, oth2, add_assoc] using
      APC_triangle_lapex hc 0 1 2 (by decide) (by decide) (by decide)

private lemma APC_total_vector_zero (hc : IsPathConfig c X Y s) :
    (∑ i : Fin 4, ∑ l : Fin 4, if l ≠ i then apexTerm c i l else 0) = 0 := by
  let A : Pt := ∑ i : Fin 4, ∑ l : Fin 4, if l ≠ i then apexTerm c i l else 0
  have hterm (r i l : Fin 4) :
      inner ℝ (c r - c 0) (if l ≠ i then apexTerm c i l else 0) =
        (if r = l then √(Hpoly X Y s) / 8 *
          (if l ≠ i then Lapex c i (oth1 i l) (oth2 i l) else 0) else 0) -
        (if (0 : Fin 4) = l then √(Hpoly X Y s) / 8 *
          (if l ≠ i then Lapex c i (oth1 i l) (oth2 i l) else 0) else 0) := by
    by_cases hli : l ≠ i
    · rw [if_pos hli, show c r - c 0 = (c r - c i) - (c 0 - c i) by abel,
        inner_sub_left, bulk_apex_anchor hc i l r hli.symm, bulk_apex_anchor hc i l 0 hli.symm]
      simp only [if_pos hli]
      split_ifs <;> ring
    · simp [hli]
  have hface (r l : Fin 4) :
      inner ℝ (c r - c 0) (∑ i : Fin 4, if l ≠ i then apexTerm c i l else 0) =
        (if r = l then √(Hpoly X Y s) / 4 else 0) -
        (if (0 : Fin 4) = l then √(Hpoly X Y s) / 4 else 0) := by
    rw [inner_sum]
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_ite_irrel,
      ← Finset.mul_sum, APC_face_lapex hc]
    split_ifs <;> ring
  have horth (r : Fin 4) : inner ℝ (c r - c 0) A = 0 := by
    dsimp [A]
    rw [Finset.sum_comm, inner_sum]
    simp_rw [hface]
    simp [Finset.sum_sub_distrib]
  have hsp : Submodule.span ℝ (Set.range (fun r : Fin 4 => c r - c 0)) = ⊤ := by
    have hv := (tetrahedron_metric hc).2.2.1.vectorSpan_eq_top_of_card_eq_finrank_add_one
      (by simp [HardSphereB5.Lean.Pt])
    rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_range_self (0 : Fin 4))] at hv
    have himage : ((fun a : Pt => a -ᵥ c 0) '' Set.range c) =
        Set.range (fun r : Fin 4 => c r - c 0) := by
      ext v
      constructor
      · rintro ⟨p, ⟨r, rfl⟩, rfl⟩
        exact ⟨r, rfl⟩
      · rintro ⟨r, rfl⟩
        exact ⟨c r, ⟨r, rfl⟩, rfl⟩
    rwa [himage] at hv
  have hall (v : Pt) (hv : v ∈ Submodule.span ℝ (Set.range (fun r : Fin 4 => c r - c 0))) :
      inner ℝ v A = 0 := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨r, rfl⟩ := hv
        exact horth r
    | zero => simp
    | add v w hv hw hv' hw' => simp [inner_add_left, hv', hw']
    | smul a v hv hv' => simp [inner_smul_left, hv']
  have hAmem : A ∈ Submodule.span ℝ (Set.range (fun r : Fin 4 => c r - c 0)) := by
    rw [hsp]
    trivial
  exact (inner_self_eq_zero.mp (hall A hAmem) : A = 0)

theorem proof_HardSphereB5_Lean_Geometry_PathCore_apex_position_contraction (hc : IsPathConfig c X Y s) :
  (∑ i, ∑ l, (if l≠i then inner ℝ (c i) (apexTerm c i l) else 0)) = -√(Hpoly X Y s)/4 := by
  have hterm (i l : Fin 4) :
      inner ℝ (c i - c 0) (if l ≠ i then apexTerm c i l else 0) =
        if l = 0 then -(√(Hpoly X Y s) / 8) *
          (if l ≠ i then Lapex c i (oth1 i l) (oth2 i l) else 0) else 0 := by
    by_cases hli : l ≠ i
    · rw [if_pos hli, show c i - c 0 = -(c 0 - c i) by abel, inner_neg_left,
        bulk_apex_anchor hc i l 0 hli.symm]
      simp only [if_pos hli]
      by_cases hl : l = 0
      · subst l
        simp only [if_pos rfl, eq_self, ite_true]
        ring
      · simp only [if_neg hl, if_neg (Ne.symm hl), neg_zero]
    · simp [hli]
  have hshift : (∑ i : Fin 4, ∑ l : Fin 4,
      inner ℝ (c i - c 0) (if l ≠ i then apexTerm c i l else 0)) = -√(Hpoly X Y s) / 4 := by
    simp_rw [hterm]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_irrel, ← Finset.mul_sum, APC_face_lapex hc]
    simp
    ring
  have hzero : (∑ i : Fin 4, ∑ l : Fin 4,
      inner ℝ (c 0) (if l ≠ i then apexTerm c i l else 0)) = 0 := by
    have hz := congrArg (fun v : Pt => inner ℝ (c 0) v) (APC_total_vector_zero hc)
    simpa only [inner_sum, inner_zero_right] using hz
  have hsplit (i l : Fin 4) :
      (if l ≠ i then inner ℝ (c i) (apexTerm c i l) else 0) =
        inner ℝ (c i - c 0) (if l ≠ i then apexTerm c i l else 0) +
        inner ℝ (c 0) (if l ≠ i then apexTerm c i l else 0) := by
    split_ifs <;> simp [inner_sub_left]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [hshift, hzero, add_zero]

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_apex_position_contraction
