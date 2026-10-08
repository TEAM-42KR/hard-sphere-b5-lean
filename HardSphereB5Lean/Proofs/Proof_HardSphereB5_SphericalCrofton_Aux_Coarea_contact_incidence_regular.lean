import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_inactive_sigma_subsingleton
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_arcA_image
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_B_chart_geometry
set_option autoImplicit false

open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
noncomputable section
set_option maxHeartbeats 1000000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_contact_incidence_regular
    (D p q : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hp : p ∈ FA) (hq : q ∈ FB) (hDp : dist D p = 1) (hDq : dist D q = 1)
    (hpq : 0 < dist p q) :
    Rc ‖D‖ ‖D-e‖ < 1 ∧ 0 < (sourcePhaseA D p).re ∧ 0 < (sourcePhaseB D q).re := by
  have h0 : D ≠ 0 := by intro h; exact hoff 0 (by simpa using h)
  have he : D ≠ e := by intro h; exact hoff 1 (by simpa using h)
  have hDn : ‖D‖ ≤ 1 := by simpa [Metric.mem_closedBall,dist_zero_right] using hD.1
  have hDen : ‖D-e‖ ≤ 1 := by simpa [Metric.mem_closedBall,dist_eq_norm] using hD.2
  have hpL : p ∈ LamC := ⟨(Metric.mem_sphere.mp hp.1).le,hp.2⟩
  have hqL : q ∈ LamC := ⟨hq.2,(Metric.mem_sphere.mp hq.1).le⟩
  have hu : p-D ∈ arcA D := by
    simp only [arcA,if_neg h0,Set.mem_setOf_eq]
    refine ⟨⟨?_,?_⟩,?_⟩
    · rw [← dist_eq_norm,dist_comm]
      exact hDp
    · change D+(p-D) ∈ LamC
      simpa only [add_sub_cancel] using hpL
    · simpa only [add_sub_cancel,dist_zero_right] using Metric.mem_sphere.mp hp.1
  have hv : q-D ∈ arcB D := by
    simp only [arcB,if_neg he,Set.mem_setOf_eq]
    refine ⟨⟨?_,?_⟩,?_⟩
    · rw [← dist_eq_norm,dist_comm]
      exact hDq
    · change D+(q-D) ∈ LamC
      simpa only [add_sub_cancel] using hqL
    · simpa only [add_sub_cancel] using Metric.mem_sphere.mp hq.1
  have huS : p-D ∈ SigmaD D := by
    have h := hu
    simp only [arcA,if_neg h0,Set.mem_setOf_eq] at h
    exact h.1
  have hvS : q-D ∈ SigmaD D := by
    have h := hv
    simp only [arcB,if_neg he,Set.mem_setOf_eq] at h
    exact h.1
  have hR : Rc ‖D‖ ‖D-e‖ < 1 := by
    by_contra hR
    have hsub := HardSphereB5.SphericalCrofton.Aux.Santalo.inactive_sigma_subsingleton D hD hoff (le_of_not_gt hR)
    have hh := congrArg (fun u : Pt => D+u) (hsub huS hvS)
    exact (dist_pos.mp hpq) (by simpa only [add_sub_cancel] using hh)
  have hcoord : 0 < D 0 ∧ D 0 < 1 := by
    have h : ‖D-e‖^2 = ‖D‖^2 - 2*(D 0) + 1 := by
      rw [norm_sub_sq_real]
      simp [e,EuclideanSpace.inner_single_right]
    constructor
    · nlinarith [norm_pos_iff.mpr h0,norm_nonneg (D-e)]
    · nlinarith [norm_pos_iff.mpr (sub_ne_zero.mpr he),norm_nonneg D]
  have hEA := EA_orthonormal D hoff
  have hBg := B_chart_geometry D hD hoff hR
  have hrA : 0 < rA D := by
    apply Real.sqrt_pos.mpr
    nlinarith [norm_nonneg D]
  have hrawA : 0 < ‖rawA D‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hh := hEA.norm_eq_one 0
    simp [EA,unitDir,hz] at hh
  have hrawB : 0 < ‖rawB D‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hh := hBg.1.norm_eq_one 0
    simp [EB,unitDir,hz] at hh
  have hcutA : 0 < cutA D := by
    unfold cutA
    apply div_pos _ (mul_pos (mul_pos (by norm_num) hrA) hrawA)
    simpa [e,EuclideanSpace.inner_single_right] using sub_pos.mpr hcoord.2
  have hcutB : 0 < cutB D := by
    unfold cutB
    apply div_pos _ (mul_pos (mul_pos (by norm_num) hBg.2.1) hrawB)
    simpa [e,EuclideanSpace.inner_single_right] using hcoord.1
  have hhalfA : halfA D < Real.pi/2 := Real.arccos_lt_pi_div_two.mpr hcutA
  have hhalfB : halfB D < Real.pi/2 := Real.arccos_lt_pi_div_two.mpr hcutB
  rw [arcA_image D hD hoff hR] at hu
  rw [hBg.2.2.2.2.1] at hv
  obtain ⟨α,hα,hαvec⟩ := hu
  obtain ⟨β,hβ,hβvec⟩ := hv
  have hreA : (sourcePhaseA D p).re = rA D * Real.cos α := by
    change inner ℝ (EA D 0) (p-D-(HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)) = _
    rw [← hαvec]
    have h00 : inner ℝ (EA D 0) (EA D 0) = 1 := by
      simpa using (orthonormal_iff_ite.mp hEA) 0 0
    have h01 : inner ℝ (EA D 0) (EA D 1) = 0 := by
      simpa using (orthonormal_iff_ite.mp hEA) 0 1
    simp only [u,circlePt,add_sub_cancel_left,real_inner_smul_right,
      inner_add_right,h00,h01,mul_one,mul_zero,add_zero]
  have hreB : (sourcePhaseB D q).re = rB D * Real.cos β := by
    change inner ℝ (EB D 0) (q-D-(HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D)) = _
    rw [← hβvec]
    have h00 : inner ℝ (EB D 0) (EB D 0) = 1 := by
      simpa using (orthonormal_iff_ite.mp hBg.1) 0 0
    have h01 : inner ℝ (EB D 0) (EB D 1) = 0 := by
      simpa using (orthonormal_iff_ite.mp hBg.1) 0 1
    simp only [v,circlePt,add_sub_cancel_left,real_inner_smul_right,
      inner_add_right,h00,h01,mul_one,mul_zero,add_zero]
  refine ⟨hR,?_,?_⟩
  · rw [hreA]
    exact mul_pos hrA (Real.cos_pos_of_mem_Ioo ⟨by linarith [hα.1],by linarith [hα.2]⟩)
  · rw [hreB]
    exact mul_pos hBg.2.1 (Real.cos_pos_of_mem_Ioo ⟨by linarith [hβ.1],by linarith [hβ.2]⟩)
