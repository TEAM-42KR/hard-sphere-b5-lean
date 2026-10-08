import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_ArcLength_restrict_circle_arc_eq_map
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem proof_SphereGeom_arcMeasure_circle_arc (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
    (a b : ℝ) (hab : a ≤ b) (hb : b - a ≤ 2 * Real.pi) :
    arcMeasure (circlePt c (e 0) (e 1) r '' Set.Icc a b) = ENNReal.ofReal (r * (b - a)) := by
  have hc : Continuous (circlePt c (e 0) (e 1) r) := by
    unfold circlePt
    fun_prop
  have hm := congrArg (fun μ : Measure E3 => μ Set.univ)
    (SphereGeom.Aux.ArcLength.restrict_circle_arc_eq_map c e he r hr a b hab hb)
  simpa [Measure.map_apply hc.measurable, Real.volume_Icc, ENNReal.ofReal_mul hr.le] using hm
