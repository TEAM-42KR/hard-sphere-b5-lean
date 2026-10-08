import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_coordinate_integral
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_coordinate_integral :
    ∀ (f : Chart5 → ℝ) (hf : Integrable f), (∫ x, f x) = ∫ D : Pt, ∫ α : ℝ, ∫ β : ℝ,
      f (pack5 (D 0) (D 1) (D 2) α β) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_coordinate_integral
