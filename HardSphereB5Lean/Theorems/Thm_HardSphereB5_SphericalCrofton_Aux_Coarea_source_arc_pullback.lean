import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_arc_pullback
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_arc_pullback :
    ∀ (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1)
    (G : Pt → Pt → ℝ) (hG : Measurable (Function.uncurry G)), (∫ u in arcA D, ∫ v in arcB D,
      G (D+u) (D+v) / (‖D‖ * ‖D-e‖ * rA D * rB D) ∂arcMeasure ∂arcMeasure) =
    ∫ α in Set.Icc (-(halfA D)) (halfA D),
      ∫ β in Set.Icc (-(halfB D)) (halfB D),
        G (D+u D α) (D+v D β) / (‖D‖ * ‖D-e‖) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_arc_pullback
