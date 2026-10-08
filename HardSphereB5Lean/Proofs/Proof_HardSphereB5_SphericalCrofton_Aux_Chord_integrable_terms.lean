import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_bounded_comp
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_integrable_terms (K : Set Pt) (hK : MeasurableSet K) (f : Kern) :
    Integrable (fun p : Pt => if 0 < chordLen K (greatCircle p) then chordLen K (greatCircle p) else 0) dOmega ∧
    Integrable (fun p : Pt => if 0 < chordLen K (greatCircle p) then (1 : ℝ) else 0) dOmega ∧
    Integrable (fun p : Pt => if 0 < chordLen K (greatCircle p) ∧ chordLen K (greatCircle p) < π / 3 then phiK f (chordLen K (greatCircle p)) else 0) dOmega ∧
    Integrable (fun p : Pt => if chordLen K (greatCircle p) < π / 3 then phiK f (chordLen K (greatCircle p)) else 0) dOmega := by
  have hmLt : MeasurableSet {x : ℝ | 0 < x} := measurableSet_lt measurable_const measurable_id
  have hmCut : MeasurableSet {x : ℝ | x < π / 3} := measurableSet_lt measurable_id measurable_const
  have hphi : Continuous (phiK f) := by cases f <;> unfold phiK <;> fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (2 * π))).exists_bound_of_continuousOn hphi.continuousOn
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Aux.Chord.integrable_bounded_comp K hK (fun x => if 0 < x then x else 0) (measurable_id.ite hmLt measurable_const) (2 * π)
    intro x hx
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2
    · simp; positivity
  · apply Aux.Chord.integrable_bounded_comp K hK (fun x => if 0 < x then (1 : ℝ) else 0) (measurable_const.ite hmLt measurable_const) 1
    intro x hx
    split_ifs <;> norm_num
  · apply Aux.Chord.integrable_bounded_comp K hK (fun x => if 0 < x ∧ x < π / 3 then phiK f x else 0) (hphi.measurable.ite (hmLt.inter hmCut) measurable_const) (max 0 C)
    intro x hx
    split_ifs
    · exact le_trans (hC x hx) (le_max_right 0 C)
    · simpa only [norm_zero] using le_max_left (0 : ℝ) C
  · apply Aux.Chord.integrable_bounded_comp K hK (fun x => if x < π / 3 then phiK f x else 0) (hphi.measurable.ite hmCut measurable_const) (max 0 C)
    intro x hx
    split_ifs
    · exact le_trans (hC x hx) (le_max_right 0 C)
    · simpa only [norm_zero] using le_max_left (0 : ℝ) C
