import HardSphereB5Lean.Definitions.Def_Gnomonic_CapFrame
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
open SphereGeom (E3)
open Gnomonic
private lemma p6cap_radius_sq (h : ℝ) (hh : |h| < 1) :
    (Real.sqrt (1 - h ^ 2)) ^ 2 = 1 - h ^ 2 := by
  have hb := abs_lt.mp hh
  have hp : 0 < 1 - h ^ 2 := by nlinarith [sq_nonneg (1 - h), sq_nonneg (1 + h)]
  exact Real.sq_sqrt (le_of_lt hp)

private lemma p6cap_radius_pos (h : ℝ) (hh : |h| < 1) : 0 < Real.sqrt (1 - h ^ 2) := by
  apply Real.sqrt_pos.mpr
  have hb := abs_lt.mp hh
  nlinarith [sq_nonneg (1 - h), sq_nonneg (1 + h)]

private lemma p6cap_frame_reverse (a e1 e2 : E3) (F : CapFrame a e1 e2) :
    ⟪e1, a⟫ = 0 ∧ ⟪e2, a⟫ = 0 ∧ ⟪e2, e1⟫ = 0 := by
  exact ⟨(real_inner_comm a e1).trans F.ae1,
    (real_inner_comm a e2).trans F.ae2,
    (real_inner_comm e1 e2).trans F.e12⟩

private lemma p6cap_capArc_unit (a e1 e2 : E3) (h t : ℝ)
    (F : CapFrame a e1 e2) (hh : |h| < 1) :
    ⟪capArc a e1 e2 h t, capArc a e1 e2 h t⟫ = 1 := by
  obtain ⟨he1a, he2a, he21⟩ := p6cap_frame_reverse a e1 e2 F
  simp only [capArc, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, F.aa, F.e11, F.e22, F.ae1, F.ae2, F.e12,
    he1a, he2a, he21, mul_zero, mul_one, zero_mul, add_zero, zero_add]
  calc
    _ = h ^ 2 + (Real.sqrt (1 - h ^ 2)) ^ 2 *
      ((Real.sin t) ^ 2 + (Real.cos t) ^ 2) := by ring
    _ = 1 := by rw [Real.sin_sq_add_cos_sq, p6cap_radius_sq h hh]; ring

private lemma p6cap_capArc_tangent (a e1 e2 : E3) (h t : ℝ) (F : CapFrame a e1 e2) :
    ⟪capArc a e1 e2 h t, capVelocity e1 e2 h t⟫ = 0 := by
  obtain ⟨he1a, he2a, he21⟩ := p6cap_frame_reverse a e1 e2 F
  simp only [capArc, capVelocity, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, F.aa, F.e11, F.e22,
    F.ae1, F.ae2, F.e12, he1a, he2a, he21,
    mul_zero, mul_one, zero_mul, add_zero, zero_add]
  ring

private lemma p6cap_capVelocity_sq (a e1 e2 : E3) (h t : ℝ)
    (F : CapFrame a e1 e2) (hh : |h| < 1) :
    ⟪capVelocity e1 e2 h t, capVelocity e1 e2 h t⟫ = 1 - h ^ 2 := by
  obtain ⟨he1a, he2a, he21⟩ := p6cap_frame_reverse a e1 e2 F
  simp only [capVelocity, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, F.e11, F.e22, F.e12, he21,
    mul_zero, mul_one, zero_mul, add_zero, zero_add]
  calc
    _ = (Real.sqrt (1 - h ^ 2)) ^ 2 *
      ((Real.sin t) ^ 2 + (Real.cos t) ^ 2) := by ring
    _ = 1 - h ^ 2 := by rw [Real.sin_sq_add_cos_sq, p6cap_radius_sq h hh]; ring

private lemma p6cap_capVelocity_ne_zero (a e1 e2 : E3) (h t : ℝ)
    (F : CapFrame a e1 e2) (hh : |h| < 1) : capVelocity e1 e2 h t ≠ 0 := by
  intro hz
  have hs := p6cap_capVelocity_sq a e1 e2 h t F hh
  rw [hz, inner_zero_left] at hs
  have hp := p6cap_radius_pos h hh
  have hr := p6cap_radius_sq h hh
  nlinarith

private lemma p6cap_project_in_plane (n u : E3) (hn : ⟪n, n⟫ = 1) (hu : ⟪u, n⟫ ≠ 0) :
    ⟪project n u, n⟫ = 0 := by
  simp only [project, inner_sub_left, real_inner_smul_left, hn]
  rw [inv_mul_cancel₀ hu]
  ring

private theorem p6cap_projectVelocity_eq_zero_iff (n u v : E3)
    (hu : ⟪u, u⟫ = 1) (hv : ⟪u, v⟫ = 0) (hq : ⟪u, n⟫ ≠ 0) :
    projectVelocity n u v = 0 ↔ v = 0 := by
  constructor
  · intro hd
    have hi := congrArg (fun x : E3 => ⟪u, x⟫) hd
    simp only [projectVelocity, inner_add_right, real_inner_smul_right,
      hu, hv, inner_zero_right, mul_zero, mul_one, zero_add] at hi
    have hvn : ⟪v, n⟫ = 0 := by
      have hh := (div_eq_zero_iff).mp hi
      rcases hh with hh | hh
      · exact neg_eq_zero.mp hh
      · exact False.elim ((pow_ne_zero 2 hq) hh)
    have hz : ⟪u, n⟫⁻¹ • v = 0 := by simpa [projectVelocity, hvn] using hd
    exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)
  · intro hv0
    simp [projectVelocity, hv0]

private lemma p6cap_hasDerivAt_capArc (a e1 e2 : E3) (h t : ℝ) :
    HasDerivAt (capArc a e1 e2 h) (capVelocity e1 e2 h t) t := by
  have hc := (Real.hasDerivAt_cos t).smul_const e1
  have hs := (Real.hasDerivAt_sin t).smul_const e2
  have hh := (hasDerivAt_const t (h • a)).add
    ((hc.add hs).const_smul (Real.sqrt (1 - h ^ 2)))
  unfold capArc capVelocity
  simpa only [zero_add, Pi.add_def, Pi.smul_def] using hh

private lemma p6cap_contDiff_capArc (a e1 e2 : E3) (h : ℝ) :
    ContDiff ℝ 2 (capArc a e1 e2 h) := by
  exact contDiff_const.add
    ((Real.contDiff_cos.smul_const e1).add
      (Real.contDiff_sin.smul_const e2) |>.const_smul (Real.sqrt (1 - h ^ 2)))

private theorem p6cap_hasDerivAt_project {f : ℝ → E3} {v : E3} {t : ℝ} (n : E3)
    (hf : HasDerivAt f v t) (hq : ⟪f t, n⟫ ≠ 0) :
    HasDerivAt (fun s => project n (f s)) (projectVelocity n (f t) v) t := by
  have hi : HasDerivAt (fun s => ⟪f s, n⟫) ⟪v, n⟫ t := by
    simpa using hf.inner ℝ (hasDerivAt_const t n)
  have hd := ((hi.inv hq).smul hf).sub_const n
  simpa [project, projectVelocity] using hd

private lemma p6cap_contDiffAt_projectedArc (n a e1 e2 : E3) (h t : ℝ)
    (hq : ⟪capArc a e1 e2 h t, n⟫ ≠ 0) :
    ContDiffAt ℝ 2 (projectedArc n a e1 e2 h) t := by
  have hf := (p6cap_contDiff_capArc a e1 e2 h).contDiffAt (x := t)
  have hi := hf.inner ℝ (contDiffAt_const (c := n))
  exact ((hi.inv hq).smul hf).sub contDiffAt_const

theorem proof_Gnomonic_capArc_regular (n a e1 e2 : E3) (h : ℝ)
    (F : CapFrame a e1 e2) (hh : |h| < 1) (hn : ⟪n, n⟫ = 1) :
    IsOpen (visible n a e1 e2 h) ∧
    ContDiffOn ℝ 2 (projectedArc n a e1 e2 h) (visible n a e1 e2 h) ∧
    ∀ t ∈ visible n a e1 e2 h,
      ⟪projectedArc n a e1 e2 h t, n⟫ = 0 ∧
      ContDiffAt ℝ 2 (projectedArc n a e1 e2 h) t ∧
      HasDerivAt (projectedArc n a e1 e2 h)
        (projectVelocity n (capArc a e1 e2 h t) (capVelocity e1 e2 h t)) t ∧
      projectVelocity n (capArc a e1 e2 h t) (capVelocity e1 e2 h t) ≠ 0 := by
  have hopen : IsOpen (visible n a e1 e2 h) := by
    exact isOpen_lt continuous_const
      ((p6cap_contDiff_capArc a e1 e2 h).continuous.inner continuous_const)
  have hc : ∀ t ∈ visible n a e1 e2 h,
      ContDiffAt ℝ 2 (projectedArc n a e1 e2 h) t := by
    intro t ht
    exact p6cap_contDiffAt_projectedArc n a e1 e2 h t (ne_of_gt ht)
  refine ⟨hopen, (fun t ht => (hc t ht).contDiffWithinAt), ?_⟩
  intro t ht
  have hq : ⟪capArc a e1 e2 h t, n⟫ ≠ 0 := ne_of_gt ht
  refine ⟨p6cap_project_in_plane n _ hn hq, hc t ht,
    p6cap_hasDerivAt_project n (p6cap_hasDerivAt_capArc a e1 e2 h t) hq, ?_⟩
  intro hz
  have hv0 := (p6cap_projectVelocity_eq_zero_iff n _ _ (p6cap_capArc_unit a e1 e2 h t F hh)
    (p6cap_capArc_tangent a e1 e2 h t F) hq).mp hz
  exact p6cap_capVelocity_ne_zero a e1 e2 h t F hh hv0

