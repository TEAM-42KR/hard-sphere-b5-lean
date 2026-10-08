import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Arrangement_cap_circle_param
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open HardSphereB5.Lean (Pt)

theorem SphereGeom.Aux.Arrangement.cap_circle_param :
    ∀ (e1 e2 n : Pt) (hframe : Orthonormal ℝ ![e1, e2, n])
    (h : ℝ) (h0 : 0 ≤ h) (h1 : h < 1), {u : Pt | ‖u‖ = 1 ∧ inner ℝ n u = h} =
      circlePt (h • n) e1 e2 (Real.sqrt (1 - h ^ 2)) '' Set.Icc (0 : ℝ) (2 * Real.pi) :=
  @proof_SphereGeom_Aux_Arrangement_cap_circle_param
