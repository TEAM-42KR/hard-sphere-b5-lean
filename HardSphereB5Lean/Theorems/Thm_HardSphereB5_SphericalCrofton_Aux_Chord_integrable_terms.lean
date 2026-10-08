import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_terms
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.integrable_terms :
    ∀ (K : Set Pt) (hK : MeasurableSet K) (f : Kern), Integrable (fun p : Pt => if 0 < chordLen K (greatCircle p) then chordLen K (greatCircle p) else 0) dOmega ∧
    Integrable (fun p : Pt => if 0 < chordLen K (greatCircle p) then (1 : ℝ) else 0) dOmega ∧
    Integrable (fun p : Pt => if 0 < chordLen K (greatCircle p) ∧ chordLen K (greatCircle p) < π / 3 then phiK f (chordLen K (greatCircle p)) else 0) dOmega ∧
    Integrable (fun p : Pt => if chordLen K (greatCircle p) < π / 3 then phiK f (chordLen K (greatCircle p)) else 0) dOmega :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_terms
