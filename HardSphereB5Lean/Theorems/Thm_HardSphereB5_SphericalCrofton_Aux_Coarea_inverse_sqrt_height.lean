import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_inverse_sqrt_height
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.inverse_sqrt_height :
    ∀ (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1), IntervalIntegrable (fun t : ℝ => (r * r + 1 - 2 * r * t) ^ (-1 / 2 : ℝ)) MeasureTheory.volume (-1) 1 ∧ (∫ t in (-1 : ℝ)..1, (r * r + 1 - 2 * r * t) ^ (-1 / 2 : ℝ)) = 2 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_inverse_sqrt_height
