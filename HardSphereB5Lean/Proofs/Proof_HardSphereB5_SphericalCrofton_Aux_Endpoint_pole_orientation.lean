import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pole_orientation (u v : Pt) : unitDir (cross v u) = -unitDir (cross u v) ∧ inner ℝ (unitDir (cross u v)) u = 0 ∧ inner ℝ (unitDir (cross u v)) v = 0 ∧ (cross u v ≠ 0 → ‖unitDir (cross u v)‖ = 1) := by
  have hc : cross v u = -(cross u v) := by
    ext i
    fin_cases i <;> simp [cross, cross_apply] <;> ring
  have hi (a b : Pt) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_three]
    <;> ring
  have h1 : inner ℝ (cross u v) u = 0 := by
    simp [hi, cross, cross_apply]
    <;> ring
  have h2 : inner ℝ (cross u v) v = 0 := by
    simp [hi, cross, cross_apply]
    <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hc, unitDir]
  · simp [unitDir, inner_smul_left, h1]
  · simp [unitDir, inner_smul_left, h2]
  · intro hne
    have hp : 0 < ‖cross u v‖ := norm_pos_iff.mpr hne
    simp [unitDir, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), ne_of_gt hp]
