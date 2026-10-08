import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_active_cap_not_interior
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Geom.active_cap_not_interior :
    ∀ (n u : Pt) (h : ℝ)
    (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) (h0 : 0 ≤ h) (h1 : h < 1) (heq : inner ℝ n u = h), u ∉ sInterior (cap n h) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_active_cap_not_interior
