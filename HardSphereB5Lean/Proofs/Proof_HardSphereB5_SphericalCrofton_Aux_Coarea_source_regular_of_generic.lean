import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_regular_of_triple
set_option autoImplicit false

open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_regular_of_generic (x : Chart5)
    (hAnte : offAxis (sourceCenter x) ∧ sourceCenter x ∈ LamC ∧
      Rc ‖sourceCenter x‖ ‖sourceCenter x - e‖ < 1 ∧
      x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)) ∧
      x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x)) ∧
      sourceEndpointA x ∈ FA ∧ sourceEndpointB x ∈ FB ∧
      0 < dist (sourceEndpointA x) (sourceEndpointB x) ∧
      dist (sourceEndpointA x) (sourceEndpointB x) < 1)
    (hαneg : x 3 ≠ -Real.pi) (hαpos : x 3 ≠ Real.pi)
    (hβneg : x 4 ≠ -Real.pi) (hβpos : x 4 ≠ Real.pi)
    (hp2 : (sourceEndpointA x) 2 ≠ 0) (hp'2 : (sourceEndpointB x) 2 ≠ 0)
    (hT : inner ℝ (cross (u (sourceCenter x) (x 3))
      (v (sourceCenter x) (x 4))) e ≠ 0) : sourceRegular x := by
  rcases hAnte with ⟨hoff, hL, hR, hα, hβ, hpA, hpB, hdist0, hdist1⟩
  have hheight (p : Pt) (hpnorm : ‖p‖ = 1) (hpcoord : p 2 ≠ 0) : |p 0| < 1 := by
    have hsq : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1 := by
      simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, hpnorm, add_assoc] using
        (EuclideanSpace.real_norm_sq_eq p).symm
    have hs : p 0 ^ 2 < 1 := by
      nlinarith [sq_nonneg (p 1), sq_pos_of_ne_zero hpcoord]
    have hsabs : |p 0| ^ 2 < (1 : ℝ) ^ 2 := by simpa [sq_abs] using hs
    exact (sq_lt_sq₀ (abs_nonneg (p 0)) (by norm_num : (0 : ℝ) ≤ 1)).mp hsabs
  have hpnorm : ‖sourceEndpointA x‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hpA.1
  have hp'norm : ‖sourceEndpointB x - e‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hpB.1
  have hheightA := hheight (sourceEndpointA x) hpnorm hp2
  have hheightB : |(sourceEndpointB x) 0 - 1| < 1 := by
    have h2 : (sourceEndpointB x - e) 2 ≠ 0 := by simpa [e] using hp'2
    simpa [e] using hheight (sourceEndpointB x - e) hp'norm h2
  have hαIoo : x 3 ∈ Set.Ioo (-Real.pi) Real.pi := by
    have hbnd : halfA (sourceCenter x) ≤ Real.pi := Real.arccos_le_pi _
    exact ⟨lt_of_le_of_ne (by linarith [hα.1]) hαneg.symm,
      lt_of_le_of_ne (by linarith [hα.2]) hαpos⟩
  have hβIoo : x 4 ∈ Set.Ioo (-Real.pi) Real.pi := by
    have hbnd : halfB (sourceCenter x) ≤ Real.pi := Real.arccos_le_pi _
    exact ⟨lt_of_le_of_ne (by linarith [hβ.1]) hβneg.symm,
      lt_of_le_of_ne (by linarith [hβ.2]) hβpos⟩
  have hcenter := HardSphereB5.SphericalCrofton.Aux.Coarea.center_phase_regular_of_triple
    (sourceCenter x) (u (sourceCenter x) (x 3)) (v (sourceCenter x) (x 4)) hT
  have hcf : centerFrame0 (sourceEndpointB x - sourceEndpointA x) ≠ 0 := by
    simpa only [sourceEndpointA, sourceEndpointB, add_sub_add_left_eq_sub] using hcenter.1
  have hcp : centerPhase (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x) ∈
      Complex.slitPlane := hcenter.2
  have hphaseA : phase ((sourceEndpointA x) 1) ((sourceEndpointA x) 2) ∈
      Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hp2)
  have hphaseB : phase ((sourceEndpointB x) 1) ((sourceEndpointB x) 2) ∈
      Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hp'2)
  exact ⟨hoff, hL, hpA, hpB, hdist0, hdist1, hαIoo, hβIoo,
    hheightA, hheightB, hcf, hphaseA, hphaseB, hcp⟩
