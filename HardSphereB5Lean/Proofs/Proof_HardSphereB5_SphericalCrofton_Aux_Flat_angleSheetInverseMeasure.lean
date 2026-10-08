import Mathlib
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Flat_angleSheetInverseMeasure (a b : ℝ) (hb : 0 < b) :
    ((volume.restrict (Set.Ioo (a - b) (a + b))).withDensity
      (fun s => ENNReal.ofReal (1 / Real.sqrt (b ^ 2 - (s - a) ^ 2)))).map
        (fun s => Real.arccos ((a - s) / b)) =
    volume.restrict (Set.Ioo (0 : ℝ) Real.pi) := by
  let inv : ℝ → ℝ := fun s => Real.arccos ((a - s) / b)
  have harg (s : ℝ) (hs : s ∈ Set.Ioo (a-b) (a+b)) :
      (a-s)/b ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · apply (lt_div_iff₀ hb).mpr
      linarith [hs.2]
    · apply (div_lt_iff₀ hb).mpr
      linarith [hs.1]
  have hrad (s : ℝ) (hs : s ∈ Set.Ioo (a-b) (a+b)) :
      0 < b ^ 2 - (s-a) ^ 2 := by
    have hm : 0 < s-a+b := by linarith [hs.1]
    have hp : 0 < b-(s-a) := by linarith [hs.2]
    nlinarith [mul_pos hm hp]
  have himage : inv '' Set.Ioo (a-b) (a+b) = Set.Ioo (0 : ℝ) Real.pi := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Real.arccos_pos.mpr (harg s hs).2, Real.arccos_lt_pi.mpr (harg s hs).1⟩
    · intro ht
      refine ⟨a-b*Real.cos t, ?_, ?_⟩
      · have hc := Real.mapsTo_cos_Ioo ht
        constructor <;> nlinarith [mul_pos hb (by linarith [hc.1] : 0 < 1+Real.cos t),
          mul_pos hb (by linarith [hc.2] : 0 < 1-Real.cos t)]
      · unfold inv
        have hc : (a-(a-b*Real.cos t))/b = Real.cos t := by field_simp; ring
        rw [hc, Real.arccos_cos ht.1.le ht.2.le]
  have hinj : Set.InjOn inv (Set.Ioo (a-b) (a+b)) := by
    intro x hx y hy hxy
    have heq := congrArg Real.cos hxy
    dsimp [inv] at heq
    rw [Real.cos_arccos (harg x hx).1.le (harg x hx).2.le,
      Real.cos_arccos (harg y hy).1.le (harg y hy).2.le] at heq
    exact by field_simp at heq; linarith
  have hderiv (s : ℝ) (hs : s ∈ Set.Ioo (a-b) (a+b)) :
      HasDerivWithinAt inv (1 / Real.sqrt (b ^ 2 - (s-a) ^ 2))
        (Set.Ioo (a-b) (a+b)) s := by
    have hsarg := harg s hs
    have houter := Real.hasDerivAt_arccos (ne_of_gt hsarg.1) (ne_of_lt hsarg.2)
    have hinner : HasDerivAt (fun s : ℝ => (a-s)/b) (-1/b) s := by
      simpa using ((hasDerivAt_const s a).sub (hasDerivAt_id s)).div_const b
    have ht := houter.comp s hinner
    have heq : -(1 / Real.sqrt (1 - ((a-s)/b)^2)) * (-1/b) =
        1 / Real.sqrt (b^2 - (s-a)^2) := by
      have hd : 1 - ((a-s)/b)^2 = (b^2 - (s-a)^2)/b^2 := by field_simp; ring
      rw [hd, Real.sqrt_div (hrad s hs).le, Real.sqrt_sq hb.le]
      field_simp
    rw [heq] at ht
    exact ht.hasDerivWithinAt
  have hw : Measurable (fun s => ENNReal.ofReal (1 / Real.sqrt (b ^ 2 - (s-a) ^ 2))) := by
    fun_prop
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (by unfold inv; fun_prop : Measurable inv)]
  rw [lintegral_withDensity_eq_lintegral_mul _ hw
    (show Measurable (fun s => g (inv s)) from hg.comp (by unfold inv; fun_prop))]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj g
  rw [himage] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro s hs
  dsimp only [Pi.mul_apply]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (b ^ 2 - (s-a) ^ 2))]
