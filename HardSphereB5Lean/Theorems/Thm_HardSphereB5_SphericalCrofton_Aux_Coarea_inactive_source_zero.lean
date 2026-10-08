import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_inactive_source_zero
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.inactive_source_zero :
    ∀ (D : Pt) (hD : D ∈ LamC)
    (h : ¬ (offAxis D ∧ Rc ‖D‖ ‖D-e‖ < 1)) (F : Pt → Pt → ℝ), (∫ u in arcA D, ∫ v in arcB D, F u v ∂arcMeasure ∂arcMeasure) = 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_inactive_source_zero
