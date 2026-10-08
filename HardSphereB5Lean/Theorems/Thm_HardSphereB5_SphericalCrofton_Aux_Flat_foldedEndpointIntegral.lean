import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Flat_foldedEndpointIntegral
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Flat.foldedEndpointIntegral :
    ∀ (K : Pt → Pt → ℝ)
    (hq : Integrable (fun p : (ℝ × ℝ) × ℝ => K (pRep p.1.1) (pRep2 p.1.2 p.2))
      ((((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo 0 1))).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)))), (∫ p : (ℝ × ℝ) × ℝ, K (pRep p.1.1) (pRep2 p.1.2 p.2)
      ∂((((volume : Measure ℝ).restrict (Set.Ioo 0 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo 0 1))).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)))) =
      ∫ v in Dfull,
        (K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) +
          K (pRep v.1) (pRep2 v.2.1 (-chiPlus v.1 v.2.1 v.2.2))) /
            Real.sqrt (Hpoly v.1 v.2.1 v.2.2) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Flat_foldedEndpointIntegral
