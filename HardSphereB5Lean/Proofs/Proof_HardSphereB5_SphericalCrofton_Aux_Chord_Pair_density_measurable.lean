import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_density_measurable (K : Set Pt) (hK : MeasurableSet K) (f : Kern) : Measurable (Function.uncurry (fun u v : Pt => if u ∈ K ∧ v ∈ K ∧ (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0)) := by
  have hi : Measurable (fun z : Pt × Pt => inner ℝ z.1 z.2) :=
    (continuous_fst.inner continuous_snd).measurable
  have hs : MeasurableSet {z : Pt × Pt | z.1 ∈ K ∧ z.2 ∈ K ∧ (1 / 2 : ℝ) ≤ inner ℝ z.1 z.2} :=
    (hK.preimage measurable_fst).inter ((hK.preimage measurable_snd).inter
      (measurableSet_le (measurable_const (a := (1 / 2 : ℝ))) hi))
  have hw : Measurable (fun z : Pt × Pt => wK f (inner ℝ z.1 z.2)) := by
    cases f
    · exact measurable_const
    · exact hi
  exact Measurable.ite hs (ENNReal.measurable_ofReal.comp hw) measurable_const
