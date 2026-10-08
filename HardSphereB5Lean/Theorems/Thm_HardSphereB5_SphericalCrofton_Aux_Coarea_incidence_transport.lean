import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_transport
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.incidence_transport :
    ∀ (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ D ∈ LamC, ∀ p ∈ FA, ∀ p' ∈ FB,
      dist D p = 1 → dist D p' = 1 → 0 < dist p p' → dist p p' < 1 → |G D p p'| ≤ C), (∫ D in LamC, ∫ u in arcA D, ∫ v in arcB D,
      (if 0 < dist (D+u) (D+v) ∧ dist (D+u) (D+v) < 1 then
        G D (D+u) (D+v) /
          (‖D‖ * ‖D-e‖ * HardSphereB5.SphericalCrofton.Aux.MovingArc.rA D * HardSphereB5.SphericalCrofton.Aux.MovingArc.rB D)
        else 0) ∂arcMeasure ∂arcMeasure) =
      ∫ p in FA, ∫ p' in FB,
        (if 0 < dist p p' ∧ dist p p' < 1 then (dist p p')⁻¹ *
          ∫ q in {q : Pt | ‖q‖ = 1 ∧ inner ℝ q (p'-p) = 0 ∧
            midpoint ℝ p p' + √(1-dist p p'^2/4) • q ∈ LamC},
            G (midpoint ℝ p p' + √(1-dist p p'^2/4) • q) p p' ∂arcMeasure
          else 0) ∂sphereMeasure e ∂sphereMeasure 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_transport
