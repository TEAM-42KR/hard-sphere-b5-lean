import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_even_overlap
import Mathlib
set_option autoImplicit false
open MeasureTheory Real

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.even_overlap :
    ∀ (h : ℝ → ENNReal) (he : ∀ r, h (-r) = h r) (L : ℝ) (hL : 0 ≤ L), (∫⁻ r, h r * ENNReal.ofReal (min L (L - r) - max 0 (-r))) = 2 * ∫⁻ r in Set.Ioc 0 L, h r * ENNReal.ofReal (L - r) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_even_overlap
