import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_strict_finite_caps_interior
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Geom.strict_finite_caps_interior :
    ∀ (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ) (u : Pt)
    (hu : ‖u‖ = 1) (hs : ∀ m, h m < inner ℝ (n m) u), u ∈ sInterior (⋂ m, cap (n m) (h m)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_strict_finite_caps_interior
