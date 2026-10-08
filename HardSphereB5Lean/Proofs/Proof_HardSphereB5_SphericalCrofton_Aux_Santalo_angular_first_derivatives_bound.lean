import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_sigma_gram_data
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_cross_norm_sq
set_option autoImplicit false
noncomputable section
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)

private lemma triples (a b p q : Pt) :
    inner ℝ (cross a p) q = inner ℝ a (cross p q) ∧
    inner ℝ p (-cross b q) = inner ℝ b (cross p q) := by
  have hi (r s : Pt) : inner ℝ r s = r 0 * s 0 + r 1 * s 1 + r 2 * s 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]; ring
  simp_rw [hi]
  simp only [cross, WithLp.ofLp_toLp, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, PiLp.neg_apply]
  constructor <;> ring

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_angular_first_derivatives_bound (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D)
    (hC : IsChart D C) (t s : ℝ) (ht : t ∈ Set.Icc 0 C.TA) (hs : s ∈ Set.Icc 0 C.TB)
    (hx : inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1) :
    |deriv (fun z => delta D C z s) t| ≤ 1 ∧ |deriv (delta D C t) s| ≤ 1 := by
  have hn := HardSphereB5.SphericalCrofton.Aux.Geom.sigma_gram_data D hD hoff
  rcases hC with ⟨_, _, _, _, _, _, _, _, hA, hB, hdu, hdv⟩
  have hut : u D C t ∈ arcA D := by rw [hA]; exact ⟨t, ht, rfl⟩
  have hvs : v D C s ∈ arcB D := by rw [hB]; exact ⟨s, hs, rfl⟩
  have hu : ‖u D C t‖ = 1 := by
    unfold arcA at hut; split_ifs at hut <;> first | simpa using hut | exact hut.1.1
  have hv : ‖v D C s‖ = 1 := by
    unfold arcB at hvs; split_ifs at hvs <;> first | simpa using hvs | exact hvs.1.1
  let x := inner ℝ (u D C t) (v D C s)
  let S := Real.sqrt (1 - x ^ 2)
  have hS : 0 < S := Real.sqrt_pos.2 (by dsimp [x]; nlinarith [hx.1, hx.2])
  have hnorm : ‖cross (u D C t) (v D C s)‖ = S := by
    have h := SphereGeom.Aux.Santalo.cross_norm_sq (u D C t) (v D C s)
    rw [hu, hv] at h
    dsimp [S, x]
    rw [← Real.sqrt_sq (norm_nonneg (cross (u D C t) (v D C s))), h]
    norm_num
  have habs (n : Pt) (hnormn : ‖n‖ = 1) : |inner ℝ n (cross (u D C t) (v D C s))| ≤ S := by
    calc
      _ ≤ ‖n‖ * ‖cross (u D C t) (v D C s)‖ := abs_real_inner_le_norm _ _
      _ = S := by rw [hnormn, hnorm, one_mul]
  have htriple := triples (nAv D) (nBv D) (u D C t) (v D C s)
  have hxt : HasDerivAt (fun z => inner ℝ (u D C z) (v D C s))
      (inner ℝ (nAv D) (cross (u D C t) (v D C s))) t := by
    simpa only [inner_zero_right, add_zero, inner_zero_left, zero_add, htriple.1] using
      (hdu t).inner ℝ (hasDerivAt_const t (v D C s))
  have hxs : HasDerivAt (fun z => inner ℝ (u D C t) (v D C z))
      (inner ℝ (nBv D) (cross (u D C t) (v D C s))) s := by
    simpa only [inner_zero_left, zero_add, inner_zero_right, add_zero, htriple.2] using
      (hasDerivAt_const s (u D C t)).inner ℝ (hdv s)
  have hdt := ((Real.hasDerivAt_arccos (ne_of_gt hx.1) (ne_of_lt hx.2)).comp t hxt).deriv
  have hds := ((Real.hasDerivAt_arccos (ne_of_gt hx.1) (ne_of_lt hx.2)).comp s hxs).deriv
  constructor
  · change |deriv (Real.arccos ∘ (fun z => inner ℝ (u D C z) (v D C s))) t| ≤ 1
    rw [hdt]
    simpa [S, x, abs_mul, abs_neg, abs_of_pos hS, one_div, mul_comm, ← div_eq_mul_inv, abs_div] using
      (div_le_one hS).2 (habs (nAv D) hn.1)
  · change |deriv (Real.arccos ∘ (fun z => inner ℝ (u D C t) (v D C z))) s| ≤ 1
    rw [hds]
    simpa [S, x, abs_mul, abs_neg, abs_of_pos hS, one_div, mul_comm, ← div_eq_mul_inv, abs_div] using
      (div_le_one hS).2 (habs (nBv D) hn.2.1)
