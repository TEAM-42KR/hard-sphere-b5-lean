import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_density_pole_form
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_cross_norm_sq
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.density_pole_form :
    ∀ (u v τ1 τ2 : Pt) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hs : 0 < Real.sin (arccos (inner ℝ u v))), santaloDens u v τ1 τ2 = |inner ℝ (unitDir (cross u v)) τ1| * |inner ℝ (unitDir (cross u v)) τ2| / Real.sin (arccos (inner ℝ u v)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_density_pole_form
