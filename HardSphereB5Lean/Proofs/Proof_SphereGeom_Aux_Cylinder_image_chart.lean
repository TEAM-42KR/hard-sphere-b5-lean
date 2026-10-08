import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

set_option maxHeartbeats 1000000

theorem proof_SphereGeom_Aux_Cylinder_image_chart :
    let f : (Fin 3 → ℝ) → Fin 3 → ℝ := fun y =>
      ![y 0 * Real.sqrt (1 - (y 1)^2) * Real.cos (y 2),
        y 0 * Real.sqrt (1 - (y 1)^2) * Real.sin (y 2), y 0 * y 1]
    f '' {x | 0 < x 0 ∧ -1 < x 1 ∧ x 1 < 1 ∧ 0 < x 2 ∧ x 2 < 2 * Real.pi} =
      {y | y 1 ≠ 0 ∨ y 0 < 0} := by
  dsimp only
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hz : 0 < 1 - (x 1)^2 := by nlinarith [hx.2.1, hx.2.2.1]
    have hrho : 0 < x 0 * Real.sqrt (1 - (x 1)^2) :=
      mul_pos hx.1 (Real.sqrt_pos.2 hz)
    have ht : (x 0 * Real.sqrt (1 - (x 1)^2), x 2 - Real.pi) ∈ polarCoord.target := by
      change 0 < x 0 * Real.sqrt (1 - (x 1)^2) ∧
        -Real.pi < x 2 - Real.pi ∧ x 2 - Real.pi < Real.pi
      exact ⟨hrho, by linarith [hx.2.2.2.1], by linarith [hx.2.2.2.2]⟩
    have hm := polarCoord.map_target ht
    change 0 < (x 0 * Real.sqrt (1 - (x 1)^2)) * Real.cos (x 2 - Real.pi) ∨
      (x 0 * Real.sqrt (1 - (x 1)^2)) * Real.sin (x 2 - Real.pi) ≠ 0 at hm
    simp only [Real.cos_sub_pi, Real.sin_sub_pi, mul_neg, neg_pos, neg_ne_zero] at hm
    change x 0 * Real.sqrt (1 - (x 1)^2) * Real.sin (x 2) ≠ 0 ∨
      x 0 * Real.sqrt (1 - (x 1)^2) * Real.cos (x 2) < 0
    exact hm.elim Or.inr Or.inl
  · intro hy
    change y 1 ≠ 0 ∨ y 0 < 0 at hy
    let q : ℝ × ℝ := (-y 0, -y 1)
    have hq : q ∈ polarCoord.source := by
      change 0 < -y 0 ∨ -y 1 ≠ 0
      rcases hy with hy | hy
      · exact Or.inr (neg_ne_zero.mpr hy)
      · exact Or.inl (neg_pos.mpr hy)
    let p : ℝ × ℝ := polarCoord q
    have hp : 0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi :=
      polarCoord.map_source hq
    have hp0 : p.1 * Real.cos p.2 = -y 0 := congrArg Prod.fst (polarCoord.left_inv hq)
    have hp1 : p.1 * Real.sin p.2 = -y 1 := congrArg Prod.snd (polarCoord.left_inv hq)
    let r : ℝ := Real.sqrt (p.1^2 + (y 2)^2)
    have hradpos : 0 < p.1^2 + (y 2)^2 := by
      nlinarith [sq_pos_of_pos hp.1, sq_nonneg (y 2)]
    have hr : 0 < r := Real.sqrt_pos.2 hradpos
    have hrr : r^2 = p.1^2 + (y 2)^2 := Real.sq_sqrt (le_of_lt hradpos)
    have hy2 : -r < y 2 ∧ y 2 < r := by
      apply abs_lt_of_sq_lt_sq' (b := r) _ hr.le
      nlinarith [sq_pos_of_pos hp.1]
    have hzlo : -1 < y 2 / r := by
      apply (lt_div_iff₀ hr).2
      simpa only [neg_one_mul] using hy2.1
    have hzhi : y 2 / r < 1 := by
      apply (div_lt_iff₀ hr).2
      simpa only [one_mul] using hy2.2
    have hunit : 1 - (y 2 / r)^2 = (p.1 / r)^2 := by
      field_simp [hr.ne']
      nlinarith [hrr]
    have hprod : r * Real.sqrt (1 - (y 2 / r)^2) = p.1 := by
      rw [hunit, Real.sqrt_sq (le_of_lt (div_pos hp.1 hr))]
      field_simp [hr.ne']
    refine ⟨![r, y 2 / r, p.2 + Real.pi], ?_, ?_⟩
    · change 0 < r ∧ -1 < y 2 / r ∧ y 2 / r < 1 ∧
        0 < p.2 + Real.pi ∧ p.2 + Real.pi < 2 * Real.pi
      exact ⟨hr, hzlo, hzhi, by linarith [hp.2.1], by linarith [hp.2.2]⟩
    · ext i
      fin_cases i
      · change r * Real.sqrt (1 - (y 2 / r)^2) * Real.cos (p.2 + Real.pi) = y 0
        rw [hprod, Real.cos_add_pi, mul_neg, hp0, neg_neg]
      · change r * Real.sqrt (1 - (y 2 / r)^2) * Real.sin (p.2 + Real.pi) = y 1
        rw [hprod, Real.sin_add_pi, mul_neg, hp1, neg_neg]
      · change r * (y 2 / r) = y 2
        field_simp [hr.ne']
