import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_5D_reduction
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.target_5D_reduction :
    ∀ (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ D ∈ LamC, ∀ p ∈ FA, ∀ p' ∈ FB,
      dist D p = 1 → dist D p' = 1 → 0 < dist p p' → dist p p' < 1 → |G D p p'| ≤ C), ∫ p in FA, ∫ p' in FB,
        (if 0 < dist p p' ∧ dist p p' < 1 then (dist p p')⁻¹ *
          ∫ q in {q : Pt | ‖q‖ = 1 ∧ inner ℝ q (p'-p) = 0 ∧
            midpoint ℝ p p' + √(1-dist p p'^2/4) • q ∈ LamC},
            G (midpoint ℝ p p' + √(1-dist p p'^2/4) • q) p p' ∂arcMeasure
          else 0) ∂sphereMeasure e ∂sphereMeasure 0 =
      ∫ y in targetIncidence, targetTest G y :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_5D_reduction
