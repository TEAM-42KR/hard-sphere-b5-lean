import HardSphereB5Lean.Definitions.Def_SphereGeom_fixedZFrame
set_option autoImplicit false

open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_fixedZFrame_measurable : Measurable fixedZRadius ∧ Measurable fixedZA ∧ Measurable fixedZB := by
  have mr : Measurable fixedZRadius := by unfold fixedZRadius; fun_prop
  refine ⟨mr, ?_, ?_⟩
  · unfold fixedZA
    apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  · unfold fixedZB
    apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
