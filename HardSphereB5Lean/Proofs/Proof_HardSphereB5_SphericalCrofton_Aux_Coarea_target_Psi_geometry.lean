import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_targetRegular
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_center_geometry
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_circle_phase_arg_closed
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_arcA_image
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_EA_orthonormal
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_B_chart_geometry
set_option autoImplicit false

open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
noncomputable section
set_option maxHeartbeats 1000000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_Psi_geometry (y : Chart5) (hy : targetRegular y) :
    sourceCenter (Psi y) = targetCenter y ∧
    sourceEndpointA (Psi y) = targetEndpointA y ∧
    sourceEndpointB (Psi y) = targetEndpointB y ∧
    (Psi y) 3 ∈ Set.Icc (-(halfA (targetCenter y))) (halfA (targetCenter y)) ∧
    (Psi y) 4 ∈ Set.Icc (-(halfB (targetCenter y))) (halfB (targetCenter y)) := by
  let D := targetCenter y
  let p := targetEndpointA y
  let p' := targetEndpointB y
  rcases hy with ⟨hpFA,hpFB,hheightA,hheightB,hangleA,hangleB,hangleC,hz0,hz1,
    hL,hoff,hR,hframe,hphaseA,hphaseB⟩
  have hD0 : D ≠ 0 := by intro h; exact hoff 0 (by simpa [D] using h)
  have hDe : D ≠ e := by intro h; exact hoff 1 (by simpa [D] using h)
  have hcenter := target_center_geometry y hz0 (by linarith) hframe hangleC
  have hpL : p ∈ LamC := by
    refine ⟨?_,hpFA.2⟩
    exact (Metric.mem_sphere.mp hpFA.1).le
  have hp'L : p' ∈ LamC := by
    refine ⟨hpFB.2,?_⟩
    exact (Metric.mem_sphere.mp hpFB.1).le
  have hu : p-D ∈ arcA D := by
    simp only [arcA,if_neg hD0,Set.mem_setOf_eq]
    refine ⟨⟨?_,?_⟩,?_⟩
    · rw [← dist_eq_norm,dist_comm]
      exact hcenter.1
    · change D+(p-D) ∈ LamC
      simpa only [add_sub_cancel] using hpL
    · simpa only [add_sub_cancel,dist_zero_right] using Metric.mem_sphere.mp hpFA.1
  have hv : p'-D ∈ arcB D := by
    simp only [arcB,if_neg hDe,Set.mem_setOf_eq]
    refine ⟨⟨?_,?_⟩,?_⟩
    · rw [← dist_eq_norm,dist_comm]
      exact hcenter.2.1
    · change D+(p'-D) ∈ LamC
      simpa only [add_sub_cancel] using hp'L
    · simpa only [add_sub_cancel] using Metric.mem_sphere.mp hpFB.1
  have hBg := B_chart_geometry D hL hoff hR
  rw [arcA_image D hL hoff hR] at hu
  rw [hBg.2.2.2.2.1] at hv
  obtain ⟨α,hα,hαvec⟩ := hu
  obtain ⟨β,hβ,hβvec⟩ := hv
  have hrA : 0 < rA D := by
    have hn : ‖D‖ ≤ 1 := by simpa [LamC,Metric.mem_closedBall,dist_zero_right] using hL.1
    apply Real.sqrt_pos.mpr
    nlinarith [norm_nonneg D]
  have hφA : sourcePhaseA D p =
      phase (inner ℝ (EA D 0) (circlePt (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)
        (EA D 0) (EA D 1) (rA D) α - HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D))
        (inner ℝ (EA D 1) (circlePt (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)
        (EA D 0) (EA D 1) (rA D) α - HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)) := by
    unfold sourcePhaseA
    rw [← hαvec]
    rfl
  have hφB : sourcePhaseB D p' =
      phase (inner ℝ (EB D 0) (circlePt (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D)
        (EB D 0) (EB D 1) (rB D) β - HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D))
        (inner ℝ (EB D 1) (circlePt (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D)
        (EB D 0) (EB D 1) (rB D) β - HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D)) := by
    unfold sourcePhaseB
    rw [← hβvec]
    rfl
  have hαpi : α ∈ Set.Icc (-Real.pi) Real.pi := by
    have hh : halfA D ≤ Real.pi := Real.arccos_le_pi (cutA D)
    exact ⟨by linarith [hα.1],by linarith [hα.2]⟩
  have hβpi : β ∈ Set.Icc (-Real.pi) Real.pi := by
    exact ⟨by linarith [hβ.1,hBg.2.2.2.1],by linarith [hβ.2,hBg.2.2.2.1]⟩
  have hargA : Complex.arg (sourcePhaseA D p) = α := by
    rw [hφA]
    exact circle_phase_arg_closed (EA D) (EA_orthonormal D hoff)
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) (rA D) α hrA hαpi (hφA ▸ hphaseA)
  have hargB : Complex.arg (sourcePhaseB D p') = β := by
    rw [hφB]
    exact circle_phase_arg_closed (EB D) hBg.1
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D) (rB D) β hBg.2.1 hβpi (hφB ▸ hphaseB)
  have hD : sourceCenter (Psi y) = D := by
    ext i
    fin_cases i <;> simp [sourceCenter,Psi,pack5,D,e,e1,e2]
  have hαcoord : (Psi y) 3 = α := by
    simpa [Psi,pack5,D,p] using hargA
  have hβcoord : (Psi y) 4 = β := by
    simpa [Psi,pack5,D,p'] using hargB
  refine ⟨hD,?_,?_,?_,?_⟩
  · unfold sourceEndpointA
    rw [hD,hαcoord,hαvec]
    abel
  · unfold sourceEndpointB
    rw [hD,hβcoord,hβvec]
    abel
  · rw [hαcoord]
    exact hα
  · rw [hβcoord]
    exact hβ
