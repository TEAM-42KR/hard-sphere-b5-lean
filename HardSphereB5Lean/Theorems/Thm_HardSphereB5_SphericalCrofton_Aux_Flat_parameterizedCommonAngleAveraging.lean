import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Flat_parameterizedCommonAngleAveraging
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_commonAngleAveraging
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem HardSphereB5.SphericalCrofton.Aux.Flat.parameterizedCommonAngleAveraging :
    ∀ {α : Type*} [MeasurableSpace α] (η : Measure α) [SFinite η]
    (T : ℝ) (hT : 0 < T) (Q : α × (ℝ × ℝ) → ℝ)
    (hQ : Integrable Q (η.prod ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T)))))
    (hper : ∀ x : α, Function.Periodic (fun χ : ℝ => Q (x, (0, χ))) T)
    (hdiag : ∀ (x : α) (a b t : ℝ), Q (x, (a + t, b + t)) = Q (x, (a, b))), Integrable (fun p : α × ℝ => Q (p.1, (0, p.2)))
      (η.prod (volume.restrict (Ioc (-(T / 2)) (T / 2)))) ∧
      (∫ p, Q p ∂(η.prod ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))))) =
        T * ∫ p : α × ℝ, Q (p.1, (0, p.2))
          ∂(η.prod (volume.restrict (Ioc (-(T / 2)) (T / 2)))) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Flat_parameterizedCommonAngleAveraging
