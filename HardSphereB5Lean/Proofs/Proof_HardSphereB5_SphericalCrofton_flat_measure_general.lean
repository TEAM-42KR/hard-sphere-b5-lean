import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_angularEndpointReduction
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_foldedEndpointIntegral
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_flat_measure_general (K : Pt → Pt → ℝ)
    (hint : Integrable (Function.uncurry K)
      (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)))
    (hrot : ∀ R, IsAxialRotation R → ∀ p ∈ FA, ∀ p' ∈ FB, K (R p) (R p') = K p p') :
    ∫ p in FA, ∫ p' in FB, K p p' ∂(sphereMeasure e) ∂(sphereMeasure 0) =
      π / 2 * ∫ v in Dfull,
        (K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) +
            K (pRep v.1) (pRep2 v.2.1 (-chiPlus v.1 v.2.1 v.2.2))) / √(Hpoly v.1 v.2.1 v.2.2)  := by
  obtain ⟨hq, hangular⟩ := HardSphereB5.SphericalCrofton.Aux.Flat.angularEndpointReduction K hint hrot
  rw [hangular, HardSphereB5.SphericalCrofton.Aux.Flat.foldedEndpointIntegral K hq]
