import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_frame_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_iff
set_option autoImplicit false

open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section
set_option maxHeartbeats 800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_contact_distances (p q : Pt)
    (hz0 : 0 < dist p q) (hz2 : dist p q < 2)
    (hf : centerFrame0 (q-p) ≠ 0) (θ : ℝ) :
    let D := midpoint ℝ p q + Real.sqrt (1-dist p q^2/4) •
      (Real.cos θ • centerFrame0 (q-p)+Real.sin θ • centerFrame1 (q-p))
    dist D p = 1 ∧ dist D q = 1 := by
  let d := q-p
  let v := Real.cos θ • centerFrame0 d+Real.sin θ • centerFrame1 d
  have hd : d ≠ 0 := sub_ne_zero.mpr (dist_pos.mp hz0).symm
  have hb := center_frame_orthonormal d hd hf
  have hi := orthonormal_iff_ite.mp hb
  have h00 : inner ℝ (centerFrame0 d) (centerFrame0 d) = 1 := by simpa using hi 0 0
  have h11 : inner ℝ (centerFrame1 d) (centerFrame1 d) = 1 := by simpa using hi 1 1
  have h01 : inner ℝ (centerFrame0 d) (centerFrame1 d) = 0 := by simpa using hi 0 1
  have h10 : inner ℝ (centerFrame1 d) (centerFrame0 d) = 0 := by simpa using hi 1 0
  have h0n : inner ℝ (centerFrame0 d) (unitDir d) = 0 := by simpa using hi 0 2
  have h1n : inner ℝ (centerFrame1 d) (unitDir d) = 0 := by simpa using hi 1 2
  have hv2 : ‖v‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [v,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      h00,h11,h01,h10,mul_one,mul_zero,zero_mul,add_zero,zero_add]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hvn : ‖v‖ = 1 := by nlinarith [norm_nonneg v]
  have hvd : inner ℝ v d = 0 := by
    have hdn : d = ‖d‖ • unitDir d := by
      simp [unitDir,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hd)]
    rw [hdn,real_inner_smul_right]
    simp [v,inner_add_left,real_inner_smul_left,h0n,h1n]
  apply (center_circle_iff p q _ hz2).2
  exact ⟨v,hvn,hvd,rfl⟩
