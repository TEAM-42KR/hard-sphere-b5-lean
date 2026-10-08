import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem proof_SphereGeom_Aux_Arrangement_regular_circle_arc (c e1 e2 n : E3) (hframe : Orthonormal ℝ ![e1,e2,n])
    (r a b : ℝ) (hr : 0 < r) (hab : a < b) (hshort : b - a < 2 * Real.pi) :
    let γ : ℝ → E3 := fun t => circlePt c e1 e2 r (a + (b - a) * t)
    ContDiff ℝ 2 γ ∧ Set.InjOn γ (Set.Icc 0 1) ∧
      (∀ t, deriv γ t ≠ 0) ∧ γ '' Set.Icc 0 1 = circlePt c e1 e2 r '' Set.Icc a b := by
  let θ : ℝ → ℝ := fun t => a + (b - a) * t
  let γ : ℝ → E3 := fun t => circlePt c e1 e2 r (θ t)
  change ContDiff ℝ 2 γ ∧ Set.InjOn γ (Set.Icc 0 1) ∧
    (∀ t, deriv γ t ≠ 0) ∧ γ '' Set.Icc 0 1 = circlePt c e1 e2 r '' Set.Icc a b
  have hpos : 0 < b - a := sub_pos.mpr hab
  let e : Fin 2 → E3 := ![e1,e2]
  have he : Orthonormal ℝ e := by
    convert hframe.comp Fin.castSucc (Fin.castSucc_injective 2) using 1
    ext i
    fin_cases i <;> rfl
  have hmap : Set.MapsTo θ (Set.Icc 0 1) (Set.Icc a b) := by
    intro t ht
    dsimp [θ]
    constructor <;> nlinarith [ht.1, ht.2]
  have hθimage : θ '' Set.Icc 0 1 = Set.Icc a b := by
    apply Set.Subset.antisymm
    · exact hmap.image_subset
    · intro u hu
      refine ⟨(u - a) / (b - a), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (sub_nonneg.mpr hu.1) hpos.le
      · exact (div_le_one hpos).mpr (by linarith [hu.2])
      · dsimp [θ]
        field_simp
        ring
  have hcd : ContDiff ℝ 2 γ := by
    dsimp [γ, θ, circlePt]
    fun_prop
  have hinj : Set.InjOn γ (Set.Icc 0 1) := by
    have hcinj : Set.InjOn (circlePt c e1 e2 r) (Set.Icc a b) := by
      have hchord (s t : ℝ) :
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
      dsimp only [e, Matrix.cons_val_zero, Matrix.cons_val_one] at hchord
      intro s hs t ht heq
      have hd : 2*r*|Real.sin ((s-t)/2)| = 0 := by
        rw [← hchord s t, heq, dist_self]
      have hz : Real.sin ((s-t)/2) = 0 := by
        have hnr : 2*r ≠ 0 := by positivity
        exact abs_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hnr)
      have hst := (Real.sin_eq_zero_iff_of_lt_of_lt
        (by linarith [hs.1, ht.2] : -Real.pi < (s-t)/2)
        (by linarith [hs.2, ht.1] : (s-t)/2 < Real.pi)).mp hz
      linarith
    intro x hx y hy hxy
    have hθxy : θ x = θ y := hcinj (hmap hx) (hmap hy) hxy
    have hmul : (b - a) * x = (b - a) * y := by
      dsimp [θ] at hθxy
      linarith
    exact mul_left_cancel₀ (ne_of_gt hpos) hmul
  have htangent (s : ℝ) : ‖(-Real.sin s) • e1 + Real.cos s • e2‖ = 1 := by
    have hi : inner ℝ ((-Real.sin s) • e1) (Real.cos s • e2) = 0 := by
      have h12 : inner ℝ e1 e2 = 0 := by
        simpa [e] using he.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)
      simp [inner_smul_left, inner_smul_right, h12]
    have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      ((-Real.sin s) • e1) (Real.cos s • e2) hi
    have h1 : ‖e1‖ = 1 := by simpa [e] using he.norm_eq_one (0 : Fin 2)
    have h2 : ‖e2‖ = 1 := by simpa [e] using he.norm_eq_one (1 : Fin 2)
    simp only [norm_smul, Real.norm_eq_abs, h1, h2, mul_one, ← pow_two,
      sq_abs, neg_sq] at hs
    nlinarith [Real.sin_sq_add_cos_sq s,
      norm_nonneg ((-Real.sin s) • e1 + Real.cos s • e2)]
  have hderiv (t : ℝ) : HasDerivAt γ
      ((b - a) • (r • ((-Real.sin (θ t)) • e1 + Real.cos (θ t) • e2))) t := by
    have hd : HasDerivAt (circlePt c e1 e2 r)
        (r • ((-Real.sin (θ t)) • e1 + Real.cos (θ t) • e2)) (θ t) :=
      (((Real.hasDerivAt_cos (θ t)).smul_const e1).add
        ((Real.hasDerivAt_sin (θ t)).smul_const e2)).const_smul r |>.const_add c
    have hθd : HasDerivAt θ (b - a) t := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id t).const_mul (b - a)).const_add a)
    exact hd.scomp t hθd
  have hreg : ∀ t, deriv γ t ≠ 0 := by
    intro t hz
    have hn : ‖deriv γ t‖ = (b - a) * r := by
      rw [(hderiv t).deriv, norm_smul, norm_smul, htangent]
      simp [Real.norm_eq_abs, abs_of_pos hpos, abs_of_pos hr]
    rw [hz, norm_zero] at hn
    nlinarith
  refine ⟨hcd, hinj, hreg, ?_⟩
  change (circlePt c e1 e2 r ∘ θ) '' Set.Icc 0 1 = _
  rw [Set.image_comp, hθimage]
