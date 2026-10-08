import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_rho_squared_distance (s : ℝ) (hs0 : 0 < s) (hs4 : s < 4) :
    rhoK .one (1 - s / 2) = 4 * (s - 1) / (s * (4 - s)) ∧
      rhoK .cos (1 - s / 2) = (s - 1) * (3 - s) / (s * (4 - s)) := by
  have hs : s ≠ 0 := ne_of_gt hs0
  have h4 : (4 : ℝ) - s ≠ 0 := (by linarith : (0 : ℝ) < 4 - s).ne'
  have hden : 1 - (1 - s / 2) ^ 2 = s * (4 - s) / 4 := by ring
  constructor
  · simp only [rhoK]; rw [hden]; field_simp; ring
  · simp only [rhoK]; rw [hden]; field_simp; ring

