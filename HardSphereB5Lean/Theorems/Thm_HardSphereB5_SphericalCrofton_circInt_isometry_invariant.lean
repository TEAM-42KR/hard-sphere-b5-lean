import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_circInt_isometry_invariant
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.circInt_isometry_invariant :
    ∀ (p p' : Pt) (R : Pt ≃ₗᵢ[ℝ] Pt) (hR : R e = e), circInt (R p) (R p') = circInt p p' :=
  @proof_HardSphereB5_SphericalCrofton_circInt_isometry_invariant
