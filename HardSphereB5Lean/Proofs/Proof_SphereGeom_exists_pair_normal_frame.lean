import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

set_option maxHeartbeats 1000000
open SphereGeom

theorem proof_SphereGeom_exists_pair_normal_frame (v w : E3)
    (hG : 0 < ‖v‖ ^ 2 * ‖w‖ ^ 2 - (inner ℝ v w) ^ 2) :
    ∃ e : Fin 3 → E3, Orthonormal ℝ e ∧
      v = ‖v‖ • e 0 ∧
      w = (inner ℝ v w / ‖v‖) • e 0 +
        Real.sqrt (‖w‖ ^ 2 - (inner ℝ v w / ‖v‖) ^ 2) • e 1 := by
  classical
  have hv0 : ‖v‖ ≠ 0 := by
    intro hv
    rw [hv] at hG
    nlinarith [sq_nonneg (inner ℝ v w)]
  have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv0)
  let a : E3 := ‖v‖⁻¹ • v
  let p : ℝ := inner ℝ v w / ‖v‖
  let u : E3 := w - p • a
  let b : E3 := ‖u‖⁻¹ • u
  have hna : ‖a‖ = 1 := by
    simp [a, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), hv0]
  have haa : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, hna]; norm_num
  have haw : inner ℝ a w = p := by
    simp [a, p, real_inner_smul_left, div_eq_mul_inv, mul_comm]
  have hwa : inner ℝ w a = p := by rw [real_inner_comm]; exact haw
  have hau : inner ℝ a u = 0 := by
    simp [u, inner_sub_right, inner_smul_right, haw, haa, hna]
  have husq : ‖u‖ ^ 2 = ‖w‖ ^ 2 - p ^ 2 := by
    dsimp [u]
    rw [norm_sub_sq_real]
    simp only [inner_smul_right, hwa, norm_smul, Real.norm_eq_abs, hna, mul_one, sq_abs]
    ring
  have hRmul : ‖v‖ ^ 2 * (‖w‖ ^ 2 - p ^ 2) =
      ‖v‖ ^ 2 * ‖w‖ ^ 2 - (inner ℝ v w) ^ 2 := by
    dsimp [p]
    field_simp [hv0] <;> ring
  have hR : 0 < ‖w‖ ^ 2 - p ^ 2 := by
    have hm : 0 < ‖v‖ ^ 2 * (‖w‖ ^ 2 - p ^ 2) := by rw [hRmul]; exact hG
    by_contra hn
    have : ‖v‖ ^ 2 * (‖w‖ ^ 2 - p ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_gt hn)
    linarith
  have hup : 0 < ‖u‖ := by nlinarith [norm_nonneg u]
  have hu0 : ‖u‖ ≠ 0 := ne_of_gt hup
  have hnb : ‖b‖ = 1 := by
    simp [b, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), hu0]
  have hab : inner ℝ a b = 0 := by simp [b, inner_smul_right, hau]
  have hba : inner ℝ b a = 0 := by rw [real_inner_comm]; exact hab
  have hsqrt : Real.sqrt (‖w‖ ^ 2 - p ^ 2) = ‖u‖ := by
    rw [← husq, Real.sqrt_sq (norm_nonneg u)]
  let g : Fin 3 → E3 := fun i => if i = 0 then a else b
  let s : Set (Fin 3) := {0, 1}
  have hs (i : s) : (i : Fin 3) = 0 ∨ (i : Fin 3) = 1 := by
    simpa only [s, Set.mem_insert_iff, Set.mem_singleton_iff] using i.property
  have hg : Orthonormal ℝ (s.domRestrict g) := by
    constructor
    · intro i
      change ‖g (i : Fin 3)‖ = 1
      rcases hs i with hi | hi <;> simp [g, hi, hna, hnb]
    · intro i j hij
      change inner ℝ (g (i : Fin 3)) (g (j : Fin 3)) = 0
      rcases hs i with hi | hi <;> rcases hs j with hj | hj
      · exact False.elim (hij (Subtype.ext (hi.trans hj.symm)))
      · simpa [g, hi, hj] using hab
      · simpa [g, hi, hj] using hba
      · exact False.elim (hij (Subtype.ext (hi.trans hj.symm)))
  obtain ⟨e, he⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp [E3] : Module.finrank ℝ E3 = Fintype.card (Fin 3)) hg
  have he0 : e 0 = a := by simpa [g] using he 0 (by simp [s])
  have he1 : e 1 = b := by simpa [g] using he 1 (by simp [s])
  refine ⟨e, e.orthonormal, ?_, ?_⟩
  · rw [he0]
    simp [a, smul_smul, hv0]
  · change w = p • e 0 + Real.sqrt (‖w‖ ^ 2 - p ^ 2) • e 1
    rw [he0, he1, hsqrt]
    simp [b, smul_smul, hu0, u]
