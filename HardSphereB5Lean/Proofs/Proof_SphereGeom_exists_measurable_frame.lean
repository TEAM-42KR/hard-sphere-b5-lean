import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
noncomputable section
theorem proof_SphereGeom_exists_measurable_frame : ∃ F₁ F₂ : E3 → E3, Measurable F₁ ∧ Measurable F₂ ∧
    ∀ p, ‖p‖ = 1 → Orthonormal ℝ ![F₁ p, F₂ p, p] := by
  let r : E3 → ℝ := fun p => Real.sqrt (p 0 ^ 2 + p 1 ^ 2)
  let F₁ : E3 → E3 := fun p => if p 0 ^ 2 + p 1 ^ 2 = 0 then WithLp.toLp 2 ![1,0,0]
    else WithLp.toLp 2 ![-p 1 / r p, p 0 / r p, 0]
  let F₂ : E3 → E3 := fun p => if p 0 ^ 2 + p 1 ^ 2 = 0 then WithLp.toLp 2 ![0,1,0]
    else WithLp.toLp 2 ![-p 2 * p 0 / r p, -p 2 * p 1 / r p, r p]
  have hm : Measurable (fun p : E3 => p 0 ^ 2 + p 1 ^ 2) := by fun_prop
  have mr : Measurable r := by dsimp [r]; fun_prop
  have hms : MeasurableSet {p : E3 | p 0 ^ 2 + p 1 ^ 2 = 0} := hm (measurableSet_singleton 0)
  refine ⟨F₁, F₂, ?_, ?_, ?_⟩
  · apply Measurable.ite hms
    · fun_prop
    · apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
      apply measurable_pi_iff.mpr
      intro i; fin_cases i <;> simp [r] <;> fun_prop
  · apply Measurable.ite hms
    · fun_prop
    · apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
      apply measurable_pi_iff.mpr
      intro i; fin_cases i <;> simp [r] <;> fun_prop
  · intro p hp
    have hp2 : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1 := by
      simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, hp, add_assoc] using
        (EuclideanSpace.real_norm_sq_eq p).symm
    have hr2 : r p ^ 2 = p 0 ^ 2 + p 1 ^ 2 := Real.sq_sqrt (by positivity)
    apply orthonormal_iff_ite.mpr
    intro i j
    simp only [PiLp.inner_apply]
    by_cases h : p 0 ^ 2 + p 1 ^ 2 = 0
    · have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      have h2 : p 2 ^ 2 = 1 := by nlinarith
      fin_cases i <;> fin_cases j <;>
        simp [F₁, F₂, h, PiLp.inner_apply, Fin.sum_univ_succ, h0, h1, ← sq, h2]
    · have hr0 : r p ≠ 0 := by intro hh; rw [hh] at hr2; simp at hr2; exact h hr2.symm
      fin_cases i <;> fin_cases j <;>
        simp [F₁, F₂, h, PiLp.inner_apply, Fin.sum_univ_succ]
      all_goals field_simp [hr0]
      all_goals nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2),
        congrArg (fun a : ℝ => p 2 * a) hr2]
