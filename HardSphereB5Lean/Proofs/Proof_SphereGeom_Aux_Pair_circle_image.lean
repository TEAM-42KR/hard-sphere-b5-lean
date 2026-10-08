import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
noncomputable section
set_option maxHeartbeats 800000
theorem proof_SphereGeom_Aux_Pair_circle_image (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁, v₂, p]) :
    circlePt 0 v₁ v₂ 1 '' Set.Icc (-Real.pi) Real.pi = greatCircle p := by
  let e : Fin 3 → E3 := ![v₁, v₂, p]
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range e) := by
    apply Eq.ge
    apply hv.linearIndependent.span_eq_top_of_card_eq_finrank
    simp [E3]
  let b : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk hv hspan
  have hb (i : Fin 3) : b i = e i := by simp [b, e]
  have hb0 : b 0 = v₁ := by simp [hb, e]
  have hb1 : b 1 = v₂ := by simp [hb, e]
  have hb2 : b 2 = p := by simp [hb, e]
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · have hc : circlePt 0 v₁ v₂ 1 t = b.repr.symm (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0]) := by
        rw [← b.sum_repr_symm]
        simp [Fin.sum_univ_succ, hb0, hb1, hb2, circlePt]
      rw [hc, b.repr.symm.norm_map]
      have hs : ‖(WithLp.toLp 2 ![Real.cos t, Real.sin t, 0] : E3)‖ ^ 2 = 1 := by
        simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Real.cos_sq_add_sin_sq]
      nlinarith [norm_nonneg (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0] : E3)]
    · have h1 : inner ℝ p v₁ = 0 := by simpa [e] using hv.inner_eq_zero (show (2 : Fin 3) ≠ 0 by decide)
      have h2 : inner ℝ p v₂ = 0 := by simpa [e] using hv.inner_eq_zero (show (2 : Fin 3) ≠ 1 by decide)
      simp [circlePt, inner_add_right, inner_smul_right, h1, h2]
  · rintro ⟨hu, hup⟩
    have hpcoord : b.repr u 2 = 0 := by simpa [b.repr_apply_apply, hb2] using hup
    have hnorm : b.repr u 0 ^ 2 + b.repr u 1 ^ 2 = 1 := by
      have h : ‖b.repr u‖ ^ 2 = 1 := by rw [b.repr.norm_map, hu]; norm_num
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simpa [Fin.sum_univ_succ, hpcoord] using h
    let z : ℂ := ⟨b.repr u 0, b.repr u 1⟩
    have hzn : ‖z‖ = 1 := by
      have h : ‖z‖ ^ 2 = 1 := by
        rw [Complex.sq_norm]
        simpa [Complex.normSq, z, pow_two] using hnorm
      nlinarith [norm_nonneg z]
    have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; norm_num at hzn
    refine ⟨z.arg, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
    have hc : Real.cos z.arg = b.repr u 0 := by simpa [Complex.cos_arg hz, hzn, z]
    have hs : Real.sin z.arg = b.repr u 1 := by simpa [Complex.sin_arg, hzn, z]
    rw [circlePt, zero_add, one_smul, hc, hs]
    have h := b.sum_repr u
    simpa [Fin.sum_univ_succ, hb0, hb1, hb2, hpcoord] using h
