import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom
open scoped Pointwise

theorem proof_SphereGeom_Aux_ConvexCone_positive_smul_transport (C : Set E3)
    (hscale : ∀ (r : ℝ), 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (r : ℝ) (hr : 0 < r) (x : E3) :
    (r • x ∈ interior C ↔ x ∈ interior C) ∧
      (r • x ∈ frontier C ↔ x ∈ frontier C) := by
  have heq : r • C = C := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hscale r hr.le z hz
    · intro hy
      refine ⟨r⁻¹ • y, hscale r⁻¹ (inv_pos.mpr hr).le y hy, ?_⟩
      simp [smul_smul, ne_of_gt hr]
  have hi : interior C = r • interior C := by
    rw [← interior_smul₀ (ne_of_gt hr), heq]
  have hc : closure C = r • closure C := by
    rw [← closure_smul₀ r C, heq]
  have hi' : r • x ∈ interior C ↔ x ∈ interior C := by
    conv_lhs => rw [hi]
    simp [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hr), smul_smul, ne_of_gt hr]
  have hc' : r • x ∈ closure C ↔ x ∈ closure C := by
    conv_lhs => rw [hc]
    simp [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hr), smul_smul, ne_of_gt hr]
  exact ⟨hi', by simp only [frontier, Set.mem_sdiff, hc', hi']⟩
