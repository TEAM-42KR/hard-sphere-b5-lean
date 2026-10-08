import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_density_measurable
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Pair.density_measurable :
    ∀ (K : Set Pt) (hK : MeasurableSet K) (f : Kern), Measurable (Function.uncurry (fun u v : Pt => if u ∈ K ∧ v ∈ K ∧ (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_density_measurable
