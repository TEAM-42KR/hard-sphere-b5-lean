import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_HitMass_support_interior_nonzero (C : Set Pt) (n : Pt) (hn : n ≠ 0)
    (hs : ∀ v ∈ C, 0 ≤ inner ℝ n v) {v : Pt} (hv : v ∈ interior C) : v ≠ 0 := by
  intro hv0
  rw [hv0] at hv
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hv)
  let t := ε / (2 * ‖n‖)
  have hnorm : 0 < ‖n‖ := norm_pos_iff.mpr hn
  have ht : 0 < t := div_pos hε (by positivity)
  have htn : t * ‖n‖ = ε / 2 := by dsimp [t]; field_simp <;> ring
  have hmem : -(t • n) ∈ C := hball (by
    rw [Metric.mem_ball, dist_zero_right, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht, htn]
    linarith)
  have hbad := hs _ hmem
  rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hbad
  have hsq : 0 < ‖n‖ ^ 2 := sq_pos_of_pos hnorm
  have hlt := mul_pos ht hsq
  linarith
