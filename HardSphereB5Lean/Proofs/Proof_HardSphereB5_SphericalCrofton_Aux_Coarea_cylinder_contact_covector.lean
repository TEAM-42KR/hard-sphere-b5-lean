import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom
set_option maxHeartbeats 600000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_cylinder_contact_covector
    (p u w : SphereGeom.E3) (htan : inner ℝ p w = 0)
    (hR : p 1 ^ 2 + p 2 ^ 2 ≠ 0) :
    let R : ℝ := p 1 ^ 2 + p 2 ^ 2
    let α : ℝ := u 0 - p 0 * (p 1 * u 1 + p 2 * u 2) / R
    let β : ℝ := p 1 * u 2 - p 2 * u 1
    (α * w 0 + β * ((p 1 * w 2 - p 2 * w 1) / R) = inner ℝ u w) ∧
      (SphereGeom.cross p u) 0 = β ∧
      (p 1 * (SphereGeom.cross p u) 2 - p 2 * (SphereGeom.cross p u) 1) / R = -α  := by
  dsimp only
  have ht : p 0 * w 0 + p 1 * w 1 + p 2 * w 2 = 0 := by
    simpa [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc] using htan
  refine ⟨?_, ?_, ?_⟩
  · simp [PiLp.inner_apply, Fin.sum_univ_succ]
    field_simp [hR]
    linear_combination -(p 1 * u 1 + p 2 * u 2) * ht
  · simp [SphereGeom.cross, cross_apply]
  · simp [SphereGeom.cross, cross_apply]
    field_simp [hR]
    ring
