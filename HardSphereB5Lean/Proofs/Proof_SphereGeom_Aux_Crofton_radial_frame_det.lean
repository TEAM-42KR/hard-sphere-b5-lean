import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

set_option backward.isDefEq.respectTransparency false in
theorem proof_SphereGeom_Aux_Crofton_radial_frame_det (a b g ap bp gp : E3) (r θ : ℝ)
    (hab : cross a b = g)
    (ha : inner ℝ ap g = -inner ℝ a gp)
    (hb : inner ℝ bp g = -inner ℝ b gp) :
    Matrix.det (fun i j : Fin 3 =>
      (![r • (Real.cos θ • ap + Real.sin θ • bp),
         r • (-Real.sin θ • a + Real.cos θ • b),
         Real.cos θ • a + Real.sin θ • b] : Fin 3 → E3) j i) =
      r ^ 2 * inner ℝ (Real.cos θ • a + Real.sin θ • b) gp := by
  have htrig := Real.cos_sq_add_sin_sq θ
  have hx : inner ℝ (Real.cos θ • ap + Real.sin θ • bp) g =
      -inner ℝ (Real.cos θ • a + Real.sin θ • b) gp := by
    simp only [inner_add_left, real_inner_smul_left, ha, hb]
    ring
  have hpol : Matrix.det (fun i j : Fin 3 =>
      (![r • (Real.cos θ • ap + Real.sin θ • bp),
         r • (-Real.sin θ • a + Real.cos θ • b),
         Real.cos θ • a + Real.sin θ • b] : Fin 3 → E3) j i) =
      -r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) *
        inner ℝ (Real.cos θ • ap + Real.sin θ • bp) (cross a b) := by
    change Matrix.det (Matrix.transpose
      ![WithLp.ofLp (r • (Real.cos θ • ap + Real.sin θ • bp)),
        WithLp.ofLp (r • (-Real.sin θ • a + Real.cos θ • b)),
        WithLp.ofLp (Real.cos θ • a + Real.sin θ • b)]) = _
    rw [Matrix.det_transpose]
    rw [Matrix.det_fin_three]
    change (r * (Real.cos θ * ap 0 + Real.sin θ * bp 0)) * (r * (-Real.sin θ * a 1 + Real.cos θ * b 1)) * (Real.cos θ * a 2 + Real.sin θ * b 2) - (r * (Real.cos θ * ap 0 + Real.sin θ * bp 0)) * (r * (-Real.sin θ * a 2 + Real.cos θ * b 2)) * (Real.cos θ * a 1 + Real.sin θ * b 1) - (r * (Real.cos θ * ap 1 + Real.sin θ * bp 1)) * (r * (-Real.sin θ * a 0 + Real.cos θ * b 0)) * (Real.cos θ * a 2 + Real.sin θ * b 2) + (r * (Real.cos θ * ap 1 + Real.sin θ * bp 1)) * (r * (-Real.sin θ * a 2 + Real.cos θ * b 2)) * (Real.cos θ * a 0 + Real.sin θ * b 0) + (r * (Real.cos θ * ap 2 + Real.sin θ * bp 2)) * (r * (-Real.sin θ * a 0 + Real.cos θ * b 0)) * (Real.cos θ * a 1 + Real.sin θ * b 1) - (r * (Real.cos θ * ap 2 + Real.sin θ * bp 2)) * (r * (-Real.sin θ * a 1 + Real.cos θ * b 1)) * (Real.cos θ * a 0 + Real.sin θ * b 0) = _
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
    have h0 : (cross a b) 0 = a 1 * b 2 - a 2 * b 1 := rfl
    have h1 : (cross a b) 1 = a 2 * b 0 - a 0 * b 2 := rfl
    have h2 : (cross a b) 2 = a 0 * b 1 - a 1 * b 0 := rfl
    rw [h0, h1, h2]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hpol, hab, hx, htrig]
  ring
