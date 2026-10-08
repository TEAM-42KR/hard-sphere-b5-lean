import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false
open SphereGeom
open HardSphereB5.Lean (Pt)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_cross_identities (x y u : Pt) :
    inner ℝ x (cross x y) = 0 ∧ inner ℝ y (cross x y) = 0 ∧
    inner ℝ (cross x y) (cross x y) = inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2 ∧
    (inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2) • u =
      (inner ℝ y y * inner ℝ x u - inner ℝ x y * inner ℝ y u) • x +
      (inner ℝ x x * inner ℝ y u - inner ℝ x y * inner ℝ x u) • y +
      (inner ℝ (cross x y) u) • cross x y := by
  have hi (v w : Pt) : inner ℝ v w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_three]
    <;> ring
  have hc (v w : Pt) : cross v w = WithLp.toLp 2
      ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hi]
    simp [hc]; ring
  · simp only [hi]
    simp [hc]; ring
  · simp only [hi]
    simp [hc]; ring
  · simp only [hi]
    ext i
    fin_cases i <;> simp [hc] <;> ring
