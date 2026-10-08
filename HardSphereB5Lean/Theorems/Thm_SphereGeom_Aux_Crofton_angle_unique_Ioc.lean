import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_angle_unique_Ioc
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
set_option autoImplicit false

theorem SphereGeom.Aux.Crofton.angle_unique_Ioc :
    ∀ (a b g x : SphereGeom.E3) (hframe : Orthonormal ℝ ![a, b, g]) (hcross : SphereGeom.cross a b = g) (hx : x ≠ 0) (hxg : inner ℝ x g = 0), ∃! ψ : ℝ, ψ ∈ Set.Ioc 0 (2 * Real.pi) ∧ x = ‖x‖ • (Real.cos ψ • a + Real.sin ψ • b) :=
  @proof_SphereGeom_Aux_Crofton_angle_unique_Ioc
