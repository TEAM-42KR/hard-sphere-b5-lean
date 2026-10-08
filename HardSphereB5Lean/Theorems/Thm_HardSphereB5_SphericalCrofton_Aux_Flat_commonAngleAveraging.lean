import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Flat_commonAngleAveraging
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem HardSphereB5.SphericalCrofton.Aux.Flat.commonAngleAveraging :
    ∀ (T : ℝ) (hT : 0 < T) (Q : ℝ × ℝ → ℝ)
    (hQ : Integrable Q ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))))
    (hper : Function.Periodic (fun χ : ℝ => Q (0, χ)) T)
    (hdiag : ∀ α β t : ℝ, Q (α + t, β + t) = Q (α, β)), IntegrableOn (fun χ : ℝ => Q (0, χ)) (Ioc (-(T / 2)) (T / 2)) ∧
      (∫ p, Q p ∂((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T)))) =
        T * ∫ χ in Ioc (-(T / 2)) (T / 2), Q (0, χ) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Flat_commonAngleAveraging
