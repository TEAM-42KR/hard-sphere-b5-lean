import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

private theorem SphereGeom.Aux.ArcLength.chord_eq (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (s t : ℝ) :
    dist (circlePt c (e 0) (e 1) r s) (circlePt c (e 0) (e 1) r t) =
      2 * r * |Real.sin ((s - t) / 2)| := by
  have hi : inner ℝ ((Real.cos s - Real.cos t) • e 0)
      ((Real.sin s - Real.sin t) • e 1) = 0 := by
    simp [inner_smul_left, inner_smul_right, he.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)]
  have hsub : circlePt c (e 0) (e 1) r s - circlePt c (e 0) (e 1) r t =
      r • ((Real.cos s - Real.cos t) • e 0 + (Real.sin s - Real.sin t) • e 1) := by
    unfold circlePt
    module
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    ((Real.cos s - Real.cos t) • e 0) ((Real.sin s - Real.sin t) • e 1) hi
  simp only [norm_smul, Real.norm_eq_abs, he.norm_eq_one, mul_one, ← pow_two, sq_abs] at hn
  have htrig : (Real.cos s - Real.cos t) ^ 2 + (Real.sin s - Real.sin t) ^ 2 =
      4 * Real.sin ((s - t) / 2) ^ 2 := by
    have h1 := Real.sin_sq_add_cos_sq s
    have h2 := Real.sin_sq_add_cos_sq t
    have h3 := Real.cos_sub s t
    have h4 := Real.cos_two_mul ((s - t) / 2)
    have h5 := Real.sin_sq_add_cos_sq ((s - t) / 2)
    rw [show 2 * ((s - t) / 2) = s - t by ring] at h4
    nlinarith
  have hn2 : ‖(Real.cos s - Real.cos t) • e 0 + (Real.sin s - Real.sin t) • e 1‖ =
      2 * |Real.sin ((s - t) / 2)| := by
    nlinarith [sq_abs (Real.sin ((s - t) / 2)),
      norm_nonneg ((Real.cos s - Real.cos t) • e 0 + (Real.sin s - Real.sin t) • e 1),
      abs_nonneg (Real.sin ((s - t) / 2))]
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hn2]
  ring
open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_ArcLength_injOn_Icc (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r)
    (a b : ℝ) (hb : b - a < 2 * Real.pi) :
    Set.InjOn (circlePt c (e 0) (e 1) r) (Set.Icc a b) := by
  intro s hs t ht heq
  have hd : 2*r*|Real.sin ((s-t)/2)| = 0 := by
    rw [← SphereGeom.Aux.ArcLength.chord_eq c e he r hr s t, heq, dist_self]
  have hz : Real.sin ((s-t)/2) = 0 := by
    have hnr : 2*r ≠ 0 := by positivity
    exact abs_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hnr)
  have hst := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hs.1, ht.2] : -Real.pi < (s-t)/2)
    (by linarith [hs.2, ht.1] : (s-t)/2 < Real.pi)).mp hz
  linarith
