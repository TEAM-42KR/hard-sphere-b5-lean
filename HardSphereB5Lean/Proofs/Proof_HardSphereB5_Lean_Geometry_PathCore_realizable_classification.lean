import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_coordinate_realization
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_tetrahedron_metric
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical
set_option maxHeartbeats 1200000

theorem proof_HardSphereB5_Lean_Geometry_PathCore_realizable_classification {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ}
    (hc : IsPathConfig c X Y s) :
    ∃ φ : Pt ≃ᵃⁱ[ℝ] Pt, ∀ i, φ (c i) = canonicalCenters X Y s i := by
  let d := canonicalCenters X Y s
  have hd : IsPathConfig d X Y s :=
    (HardSphereB5.Lean.Geometry.PathCore.coordinate_realization hc.X_pos hc.X_lt_one
      hc.Y_pos hc.Y_lt_one hc.H_pos).1
  have hci : AffineIndependent ℝ c :=
    (HardSphereB5.Lean.Geometry.PathCore.tetrahedron_metric hc).2.2.1
  have hdi : AffineIndependent ℝ d :=
    (HardSphereB5.Lean.Geometry.PathCore.tetrahedron_metric hd).2.2.1
  let ac : AffineBasis (Fin 4) ℝ Pt := ⟨c, hci,
    hci.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Pt])⟩
  let ad : AffineBasis (Fin 4) ℝ Pt := ⟨d, hdi,
    hdi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Pt])⟩
  let bc := ac.basisOf 0
  let bd := ad.basisOf 0
  have hq : ∀ i j : Fin 4, q c i j = q d i j := by
    have h01 := hc.q01.trans hd.q01.symm
    have h02 := hc.q02.trans hd.q02.symm
    have h03 := hc.q03.trans hd.q03.symm
    have h12 := hc.q12.trans hd.q12.symm
    have h13 := hc.q13.trans hd.q13.symm
    have h23 := hc.q23.trans hd.q23.symm
    have hsymm : ∀ (v : Fin 4 → Pt) (i j : Fin 4), q v i j = q v j i := by
      intro v i j
      exact congrArg (fun z : ℝ => z ^ 2) (dist_comm _ _)
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact h01 | exact h02 | exact h03 | exact h12 | exact h13 | exact h23
      | exact (hsymm c 1 0).trans (h01.trans (hsymm d 0 1))
      | exact (hsymm c 2 0).trans (h02.trans (hsymm d 0 2))
      | exact (hsymm c 3 0).trans (h03.trans (hsymm d 0 3))
      | exact (hsymm c 2 1).trans (h12.trans (hsymm d 1 2))
      | exact (hsymm c 3 1).trans (h13.trans (hsymm d 1 3))
      | exact (hsymm c 3 2).trans (h23.trans (hsymm d 2 3))
      | simp [q]
  have hn : ∀ i j : Fin 4, ‖c i - c j‖ * ‖c i - c j‖ =
      ‖d i - d j‖ * ‖d i - d j‖ := by
    intro i j
    simpa only [q, dist_eq_norm, pow_two] using hq i j
  have hg : ∀ i j : Fin 4, inner ℝ (c i - c 0) (c j - c 0) =
      inner ℝ (d i - d 0) (d j - d 0) := by
    intro i j
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    have hcsub : (c i - c 0) - (c j - c 0) = c i - c j := by abel
    have hdsub : (d i - d 0) - (d j - d 0) = d i - d j := by abel
    rw [hcsub, hdsub, hn i 0, hn j 0, hn i j]
  let e : Pt ≃ₗ[ℝ] Pt := bc.equiv bd (Equiv.refl _)
  have he : ∀ i : {j : Fin 4 // j ≠ 0}, e (bc i) = bd i := by
    intro i
    simp [e]
  have hb : ∀ i j, inner ℝ (bd i) (bd j) = inner ℝ (bc i) (bc j) := by
    intro i j
    change inner ℝ (ad.basisOf 0 i) (ad.basisOf 0 j) =
      inner ℝ (ac.basisOf 0 i) (ac.basisOf 0 j)
    rw [AffineBasis.basisOf_apply, AffineBasis.basisOf_apply,
      AffineBasis.basisOf_apply, AffineBasis.basisOf_apply]
    exact (hg i.val j.val).symm
  have hei : ∀ x y : Pt, inner ℝ (e x) (e y) = inner ℝ x y := by
    intro x y
    conv_lhs => rw [← bc.sum_repr x, ← bc.sum_repr y]
    conv_rhs => rw [← bc.sum_repr x, ← bc.sum_repr y]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      inner_smul_right, he, hb]
  let L : Pt ≃ₗᵢ[ℝ] Pt := e.isometryOfInner hei
  let φ : Pt ≃ᵃⁱ[ℝ] Pt :=
    ((AffineIsometryEquiv.vaddConst ℝ (c 0)).symm.trans
      L.toAffineIsometryEquiv).trans (AffineIsometryEquiv.vaddConst ℝ (d 0))
  refine ⟨φ, ?_⟩
  intro i
  change e (c i - c 0) + d 0 = d i
  by_cases hi : i = 0
  · simp [hi]
  · have hh : e (c i - c 0) = d i - d 0 := by
      have hh' := he ⟨i, hi⟩
      dsimp only [bc, bd] at hh'
      rw [AffineBasis.basisOf_apply, AffineBasis.basisOf_apply] at hh'
      exact hh'
    rw [hh]
    abel
