import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_canonical_closed_density_chain_rule
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.canonical_closed_density_chain_rule :
    ∀ (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1), ∃ C : Charts, IsChart D C ∧ delta D C C.TA C.TB = 0 ∧
      delta D C C.TA 0 = deltaV D ∧ delta D C 0 C.TB = deltaV D ∧ delta D C 0 0 = 0 ∧
      (∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB,
        ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) →
          inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1) ∧
      (∀ f : Kern, ∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB,
        ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) →
          J f D C t s = -Q12 f D C t s + H f D C t s) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_canonical_closed_density_chain_rule
