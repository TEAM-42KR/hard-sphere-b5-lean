import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
set_option maxHeartbeats 800000

theorem proof_SphereGeom_Aux_sphere_slice_circle_image (E : Fin 3 → E3) (hE : Orthonormal ℝ E) (z : ℝ) (hz : |z| < 1) :
    {u : E3 | ‖u‖ = 1 ∧ inner ℝ (E 2) u = z} =
      circlePt (z • E 2) (E 0) (E 1) (Real.sqrt (1 - z ^ 2)) ''
        Set.Icc (0 : ℝ) (2 * Real.pi) := by
  classical
  let B : OrthonormalBasis (Fin 3) ℝ E3 :=
    OrthonormalBasis.mk hE
      (hE.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [E3])).ge
  have hsq (v : E3) :
      (inner ℝ (E 0) v) ^ 2 + (inner ℝ (E 1) v) ^ 2 +
        (inner ℝ (E 2) v) ^ 2 = ‖v‖ ^ 2 := by
    simpa [B, Fin.sum_univ_succ, real_inner_comm, pow_two,
      real_inner_self_eq_norm_sq, add_assoc] using B.sum_inner_mul_inner v v
  have hrep (v : E3) :
      inner ℝ (E 0) v • E 0 + inner ℝ (E 1) v • E 1 +
        inner ℝ (E 2) v • E 2 = v := by
    simpa [B, Fin.sum_univ_succ, add_assoc] using B.sum_repr' v
  have hEi : ∀ i j, inner ℝ (E i) (E j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp hE
  have hz2 : z ^ 2 < 1 := by
    have hz' := abs_lt.mp hz
    nlinarith [sq_nonneg (z - 1), sq_nonneg (z + 1)]
  let r : ℝ := Real.sqrt (1 - z ^ 2)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by linarith)
  ext u
  constructor
  · rintro ⟨hun, huz⟩
    let a : ℝ := inner ℝ (E 0) u
    let b : ℝ := inner ℝ (E 1) u
    have hab : a ^ 2 + b ^ 2 = r ^ 2 := by
      have hu := hsq u
      rw [hun, huz] at hu
      dsimp [a, b]
      nlinarith
    let x : ℝ := a / r
    let y : ℝ := b / r
    have hxy : x ^ 2 + y ^ 2 = 1 := by
      dsimp [x, y]
      field_simp
      nlinarith
    have hx : -1 ≤ x ∧ x ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg y, sq_nonneg (x - 1), sq_nonneg (x + 1)]
    have hc : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
    have hs2 : Real.sin (Real.arccos x) ^ 2 = y ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (Real.arccos x)]
    have hs0 : 0 ≤ Real.sin (Real.arccos x) := by
      rw [Real.sin_arccos]
      exact Real.sqrt_nonneg _
    have ha : r * x = a := by dsimp [x]; field_simp
    have hb : r * y = b := by dsimp [y]; field_simp
    have hpoint (t : ℝ) (hct : Real.cos t = x) (hst : Real.sin t = y) :
        circlePt (z • E 2) (E 0) (E 1) r t = u := by
      rw [circlePt, hct, hst, smul_add, smul_smul, smul_smul, ha, hb]
      rw [← huz]
      simpa [add_comm, add_left_comm, add_assoc, a, b] using hrep u
    by_cases hy : 0 ≤ y
    · have hs : Real.sin (Real.arccos x) = y := by nlinarith
      refine ⟨Real.arccos x, ⟨Real.arccos_nonneg x, ?_⟩, hpoint _ hc hs⟩
      have := Real.arccos_le_pi x
      linarith [Real.pi_pos]
    · have hs : -Real.sin (Real.arccos x) = y := by
        have hy' : y < 0 := lt_of_not_ge hy
        nlinarith
      refine ⟨2 * Real.pi - Real.arccos x, ⟨?_, ?_⟩, ?_⟩
      · linarith [Real.arccos_le_pi x, Real.pi_pos]
      · linarith [Real.arccos_nonneg x]
      · apply hpoint
        · simpa only [Real.cos_two_pi_sub] using hc
        · simpa only [Real.sin_two_pi_sub] using hs
  · rintro ⟨t, ht, rfl⟩
    have h0 : inner ℝ (E 0) (circlePt (z • E 2) (E 0) (E 1) r t) =
        r * Real.cos t := by
      simp [circlePt, inner_add_right, inner_smul_right, hEi, hE.norm_eq_one]
    have h1 : inner ℝ (E 1) (circlePt (z • E 2) (E 0) (E 1) r t) =
        r * Real.sin t := by
      simp [circlePt, inner_add_right, inner_smul_right, hEi, hE.norm_eq_one]
    have h2 : inner ℝ (E 2) (circlePt (z • E 2) (E 0) (E 1) r t) = z := by
      simp [circlePt, inner_add_right, inner_smul_right, hEi, hE.norm_eq_one]
    refine ⟨?_, h2⟩
    have hu := hsq (circlePt (z • E 2) (E 0) (E 1) r t)
    rw [h0, h1, h2] at hu
    have hn : 0 ≤ ‖circlePt (z • E 2) (E 0) (E 1) r t‖ := norm_nonneg _
    nlinarith [Real.sin_sq_add_cos_sq t]
