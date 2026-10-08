import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_integral_reduction
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_integral_reduction :
    ∀ (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2)), (∫ D in LamC, ∫ U in arcA D, ∫ V in arcB D,
      (if 0 < dist (D+U) (D+V) ∧ dist (D+U) (D+V) < 1 then
        G D (D+U) (D+V) / (‖D‖ * ‖D-e‖ * rA D * rB D) else 0)
        ∂arcMeasure ∂arcMeasure) =
    ∫ D in LamC, if offAxis D ∧ Rc ‖D‖ ‖D-e‖ < 1 then
      ∫ α in Set.Icc (-(halfA D)) (halfA D),
        ∫ β in Set.Icc (-(halfB D)) (halfB D),
          (if 0 < dist (D+u D α) (D+v D β) ∧ dist (D+u D α) (D+v D β) < 1
            then G D (D+u D α) (D+v D β) / (‖D‖ * ‖D-e‖) else 0)
      else 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_integral_reduction
