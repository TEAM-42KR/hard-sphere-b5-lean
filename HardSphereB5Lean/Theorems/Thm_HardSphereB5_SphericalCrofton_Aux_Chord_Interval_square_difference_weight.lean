import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_square_difference_weight
import Mathlib
set_option autoImplicit false
open MeasureTheory Real

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.square_difference_weight :
    ∀ (h : ℝ → ENNReal) (hh : Measurable h) (L : ℝ), (∫⁻ s in Set.Ioc 0 L, ∫⁻ t in Set.Ioc 0 L, h (t - s)) = ∫⁻ r, h r * ENNReal.ofReal (min L (L - r) - max 0 (-r)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_square_difference_weight
