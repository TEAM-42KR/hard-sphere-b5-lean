import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_sphere_slice_circle_image
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open HardSphereB5.Lean (Pt)

theorem proof_SphereGeom_Aux_Arrangement_cap_circle_param (e1 e2 n : Pt) (hframe : Orthonormal ℝ ![e1, e2, n])
    (h : ℝ) (h0 : 0 ≤ h) (h1 : h < 1) :
    {u : Pt | ‖u‖ = 1 ∧ inner ℝ n u = h} =
      circlePt (h • n) e1 e2 (Real.sqrt (1 - h ^ 2)) '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
  have hh : |h| < 1 := by rwa [abs_of_nonneg h0]
  simpa using SphereGeom.Aux.sphere_slice_circle_image ![e1, e2, n] hframe h hh
