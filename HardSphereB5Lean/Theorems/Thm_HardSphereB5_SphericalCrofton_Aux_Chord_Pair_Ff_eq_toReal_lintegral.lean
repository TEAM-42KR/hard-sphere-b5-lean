import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_Ff_eq_toReal_lintegral
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Pair.Ff_eq_toReal_lintegral :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern), Ff f K = (∫⁻ u, ∫⁻ v, (fun u v : Pt => if u ∈ K ∧ v ∈ K ∧ (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0) u v ∂dOmega ∂dOmega).toReal :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_Ff_eq_toReal_lintegral
