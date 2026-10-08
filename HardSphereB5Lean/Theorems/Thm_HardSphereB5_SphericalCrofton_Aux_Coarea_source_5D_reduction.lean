import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_5D_reduction
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_5D_reduction :
    ∀ (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ D ∈ LamC, ∀ p ∈ FA, ∀ p' ∈ FB,
      dist D p = 1 → dist D p' = 1 → 0 < dist p p' → dist p p' < 1 → |G D p p'| ≤ C), (∫ D in LamC, ∫ u in arcA D, ∫ v in arcB D,
      (if 0 < dist (D+u) (D+v) ∧ dist (D+u) (D+v) < 1 then
        G D (D+u) (D+v) /
          (‖D‖ * ‖D-e‖ * HardSphereB5.SphericalCrofton.Aux.MovingArc.rA D * HardSphereB5.SphericalCrofton.Aux.MovingArc.rB D)
        else 0) ∂arcMeasure ∂arcMeasure) =
      ∫ x in sourceIncidence, sourceTest G x :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_5D_reduction
