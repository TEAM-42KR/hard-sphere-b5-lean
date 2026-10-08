import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_periodic_compact_connected_arc
import Mathlib
set_option autoImplicit false
open MeasureTheory Real
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.periodic_compact_connected_arc :
    ∀ {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : ℝ → X) (hC : Continuous C) (T : ℝ) (hT : 0 < T)
    (hper : Function.Periodic C T)
    (hinj : ∀ a b : ℝ, b - a < T → Set.InjOn C (Set.Icc a b))
    (S : Set X) (hS : IsConnected S) (hcompact : IsCompact S)
    (hsub : S ⊆ Set.range C) (cut : ℝ) (hcut : C cut ∉ S), ∃ a b : ℝ, a ≤ b ∧ b - a < T ∧ S = C '' Set.Icc a b :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_periodic_compact_connected_arc
