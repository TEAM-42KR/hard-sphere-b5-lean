import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_bounded_comp
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.integrable_bounded_comp :
    ∀ (K : Set Pt) (hK : MeasurableSet K)
    (g : ℝ → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ x ∈ Set.Icc (0 : ℝ) (2 * π), ‖g x‖ ≤ B), Integrable (fun p : Pt => g (chordLen K (greatCircle p))) dOmega :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_bounded_comp
