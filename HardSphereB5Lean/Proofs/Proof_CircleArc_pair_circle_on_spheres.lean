import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
noncomputable section
open SphereGeom
open scoped RealInnerProductSpace
theorem proof_CircleArc_pair_circle_on_spheres (a b : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (hperp : ∀ i, inner ℝ (b - a) (e i) = 0)
    (hd : dist a b < 2) (t : ℝ) :
    circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1)
      (Real.sqrt (1 - dist a b ^ 2 / 4)) t ∈ Metric.sphere a 1 ∩ Metric.sphere b 1 := by
  let r : ℝ := Real.sqrt (1 - dist a b ^ 2 / 4)
  let u : E3 := Real.cos t • e 0 + Real.sin t • e 1
  have he00 : inner ℝ (e 0) (e 0) = 1 := by
    rw [real_inner_self_eq_norm_sq, he.1 0]; norm_num
  have he11 : inner ℝ (e 1) (e 1) = 1 := by
    rw [real_inner_self_eq_norm_sq, he.1 1]; norm_num
  have he01 : inner ℝ (e 0) (e 1) = 0 := he.inner_eq_zero (by decide)
  have he10 : inner ℝ (e 1) (e 0) = 0 := he.inner_eq_zero (by decide)
  have hu : inner ℝ u u = 1 := by
    dsimp [u]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, he00, he11, he01, he10]
    nlinarith [Real.cos_sq_add_sin_sq t]
  have hvu : inner ℝ (b - a) u = 0 := by
    simp [u, inner_add_right, real_inner_smul_right, hperp]
  have huv : inner ℝ u (b - a) = 0 := by
    rw [real_inner_comm]; exact hvu
  have hv : inner ℝ (b - a) (b - a) = dist a b ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm]
  have hr : r ^ 2 = 1 - dist a b ^ 2 / 4 := by
    apply Real.sq_sqrt
    nlinarith [dist_nonneg (x := a) (y := b)]
  have hxa : circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - a =
      (1 / 2 : ℝ) • (b - a) + r • u := by
    dsimp [circlePt, u]; module
  have hxb : circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - b =
      (-1 / 2 : ℝ) • (b - a) + r • u := by
    dsimp [circlePt, u]; module
  have hna : ‖circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - a‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hxa]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hvu, huv, hv, hu]
    nlinarith [hr]
  have hnb : ‖circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - b‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hxb]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hvu, huv, hv, hu]
    nlinarith [hr]
  constructor <;> rw [Metric.mem_sphere, dist_eq_norm]
  · nlinarith [norm_nonneg (circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - a)]
  · nlinarith [norm_nonneg (circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1) r t - b)]
