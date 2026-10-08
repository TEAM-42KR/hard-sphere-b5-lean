import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pole_orientation
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.pole_orientation :
    ∀ (u v : Pt), unitDir (cross v u) = -unitDir (cross u v) ∧ inner ℝ (unitDir (cross u v)) u = 0 ∧ inner ℝ (unitDir (cross u v)) v = 0 ∧ (cross u v ≠ 0 → ‖unitDir (cross u v)‖ = 1) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pole_orientation
