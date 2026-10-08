import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Flat_angularEndpointReduction
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_endpointCylinderMeasures
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_existsAxialRotation
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_parameterizedCommonAngleAveraging
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped ENNReal

theorem HardSphereB5.SphericalCrofton.Aux.Flat.angularEndpointReduction :
    ∀ (K : Pt → Pt → ℝ)
    (hint : Integrable (Function.uncurry K)
      (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)))
    (hrot : ∀ R, IsAxialRotation R → ∀ p ∈ FA, ∀ p' ∈ FB, K (R p) (R p') = K p p'), Integrable (fun v : (ℝ × ℝ) × ℝ => K (pRep v.1.1) (pRep2 v.1.2 v.2))
      (((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) 1))).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) ∧
    (∫ p in FA, ∫ p' in FB, K p p' ∂(sphereMeasure e) ∂(sphereMeasure 0)) =
      Real.pi / 2 * ∫ v : (ℝ × ℝ) × ℝ, K (pRep v.1.1) (pRep2 v.1.2 v.2)
        ∂(((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
          (volume.restrict (Set.Ioo (0 : ℝ) 1))).prod
            (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Flat_angularEndpointReduction
