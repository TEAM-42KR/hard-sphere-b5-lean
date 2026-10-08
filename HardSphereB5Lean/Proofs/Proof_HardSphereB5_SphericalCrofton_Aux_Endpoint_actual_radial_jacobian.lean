import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
open SphereGeom HardSphereB5.SphericalCrofton
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

private theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.actual_radial_jacobian_det_formula (u v τ1 τ2 : E3) (r : ℝ) (a : E3 →L[ℝ] ℝ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hcross : cross u v ≠ 0)
    (ha2 : a (EuclideanSpace.single 2 1) = 0) :
    let n : E3 := cross u v
    let N : ℝ := ‖n‖
    let p : E3 := N⁻¹ • n
    let e : Fin 3 → E3 →L[ℝ] ℝ := fun i => PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
    let dn : E3 →L[ℝ] E3 := (e 0).smulRight (cross τ1 v) + (e 1).smulRight (cross u τ2)
    let D : E3 →L[ℝ] E3 := r • (N⁻¹ • dn + a.smulRight n) + (e 2).smulRight p
    |LinearMap.det D.toLinearMap| = r ^ 2 * |inner ℝ p τ1| * |inner ℝ p τ2| /
      Real.sin (Real.arccos (inner ℝ u v)) := by
  dsimp only
  let n : E3 := cross u v
  let N : ℝ := ‖n‖
  let p : E3 := N⁻¹ • n
  let q1 : E3 := cross τ1 v
  let q2 : E3 := cross u τ2
  let e : Fin 3 → E3 →L[ℝ] ℝ := fun i => PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
  let dn : E3 →L[ℝ] E3 := (e 0).smulRight q1 + (e 1).smulRight q2
  let dp : E3 →L[ℝ] E3 := N⁻¹ • dn + a.smulRight n
  let D : E3 →L[ℝ] E3 := r • dp + (e 2).smulRight p
  have hNpos : 0 < N := norm_pos_iff.mpr hcross
  have hNne : N ≠ 0 := hNpos.ne'
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hmat : LinearMap.toMatrix b b D.toLinearMap =
      !![r * (N⁻¹ * q1 0 + a (b 0) * n 0),
         r * (N⁻¹ * q2 0 + a (b 1) * n 0), N⁻¹ * n 0;
         r * (N⁻¹ * q1 1 + a (b 0) * n 1),
         r * (N⁻¹ * q2 1 + a (b 1) * n 1), N⁻¹ * n 1;
         r * (N⁻¹ * q1 2 + a (b 0) * n 2),
         r * (N⁻¹ * q2 2 + a (b 1) * n 2), N⁻¹ * n 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, b, D, dp, dn, e, p,
        EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, ha2, smul_eq_mul] <;> ring
  have hinner (s t : E3) : inner ℝ s t = s 0 * t 0 + s 1 * t 1 + s 2 * t 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]
    <;> ring
  have hdetRaw : LinearMap.det D.toLinearMap =
      r ^ 2 * inner ℝ n τ1 * inner ℝ n τ2 / N ^ 3 := by
    rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [hinner, q1, q2, n, SphereGeom.cross, WithLp.ofLp_toLp,
      cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp [hNne] <;> ring
  have hdet : LinearMap.det D.toLinearMap =
      r ^ 2 * inner ℝ p τ1 * inner ℝ p τ2 / N := by
    rw [hdetRaw]
    simp only [p, inner_smul_left, starRingEnd_apply, star_trivial]
    field_simp [hNne] <;> ring
  have hnsq : N ^ 2 = 1 - inner ℝ u v ^ 2 := by
    have hgram : ‖cross u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2 := by
      simp_rw [← real_inner_self_eq_norm_sq, hinner]
      simp only [SphereGeom.cross, WithLp.ofLp_toLp, cross_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      ring
    simpa [hu, hv] using hgram
  have hsin : Real.sin (Real.arccos (inner ℝ u v)) = N := by
    rw [Real.sin_arccos, ← hnsq]
    exact Real.sqrt_sq (norm_nonneg n)
  change |LinearMap.det D.toLinearMap| =
    r ^ 2 * |inner ℝ p τ1| * |inner ℝ p τ2| /
      Real.sin (Real.arccos (inner ℝ u v))
  rw [hdet, hsin, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (sq_nonneg r), abs_of_pos hNpos]

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_actual_radial_jacobian (γ1 γ2 : ℝ → E3) (τ1 τ2 : E3) (x : E3)
    (hγ1 : HasDerivAt γ1 τ1 (x 0)) (hγ2 : HasDerivAt γ2 τ2 (x 1))
    (hu : ‖γ1 (x 0)‖ = 1) (hv : ‖γ2 (x 1)‖ = 1)
    (hcross : cross (γ1 (x 0)) (γ2 (x 1)) ≠ 0) :
    let Φ : E3 → E3 := fun y => y 2 • unitDir (cross (γ1 (y 0)) (γ2 (y 1)))
    let p : E3 := unitDir (cross (γ1 (x 0)) (γ2 (x 1)))
    HasFDerivAt Φ (fderiv ℝ Φ x) x ∧
      |LinearMap.det (fderiv ℝ Φ x).toLinearMap| =
        (x 2) ^ 2 * |inner ℝ p τ1| * |inner ℝ p τ2| /
          Real.sin (Real.arccos (inner ℝ (γ1 (x 0)) (γ2 (x 1)))) := by
  dsimp only
  let u : E3 := γ1 (x 0)
  let v : E3 := γ2 (x 1)
  let n : E3 := cross u v
  let N : ℝ := ‖n‖
  let r : ℝ := x 2
  let p : E3 := N⁻¹ • n
  let Φ : E3 → E3 := fun y => y 2 • unitDir (cross (γ1 (y 0)) (γ2 (y 1)))
  let G : E3 → E3 := fun y => cross (γ1 (y 0)) (γ2 (y 1))
  let q1 : E3 := cross τ1 v
  let q2 : E3 := cross u τ2
  let e : Fin 3 → E3 →L[ℝ] ℝ := fun i => PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
  let du : E3 →L[ℝ] E3 := (e 0).smulRight τ1
  let dv : E3 →L[ℝ] E3 := (e 1).smulRight τ2
  let dn : E3 →L[ℝ] E3 := (e 0).smulRight q1 + (e 1).smulRight q2
  let cp : E3 →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi
    (fun i => q1 i • e 0 + q2 i • e 1)
  have hNpos : 0 < N := norm_pos_iff.mpr hcross
  have hNne : N ≠ 0 := hNpos.ne'
  have he (i : Fin 3) : HasFDerivAt (fun y : E3 => y i) (e i) x := (e i).hasFDerivAt
  have hdu : HasFDerivAt (fun y : E3 => γ1 (y 0)) du x := by
    apply (hγ1.hasFDerivAt.comp x (he 0)).congr_fderiv
    ext y i
    simp [du, e]
  have hdv : HasFDerivAt (fun y : E3 => γ2 (y 1)) dv x := by
    apply (hγ2.hasFDerivAt.comp x (he 1)).congr_fderiv
    ext y i
    simp [dv, e]
  have hA (i : Fin 3) : HasFDerivAt (fun y : E3 => γ1 (y 0) i) (τ1 i • e 0) x := by
    apply ((e i).hasFDerivAt.comp x hdu).congr_fderiv
    ext y
    simp [du, e, smul_eq_mul]
    ring
  have hB (i : Fin 3) : HasFDerivAt (fun y : E3 => γ2 (y 1) i) (τ2 i • e 1) x := by
    apply ((e i).hasFDerivAt.comp x hdv).congr_fderiv
    ext y
    simp [dv, e, smul_eq_mul]
    ring
  have hcoords : HasFDerivAt (fun y => WithLp.ofLp (G y)) cp x := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert ((hA 1).mul (hB 2)).sub ((hA 2).mul (hB 1)) using 1
      · ext y
        simp [G, SphereGeom.cross, cross_apply]
      · ext y
        simp [cp, q1, q2, u, v, e, SphereGeom.cross, cross_apply,
          smul_eq_mul]
        ring
    · convert ((hA 2).mul (hB 0)).sub ((hA 0).mul (hB 2)) using 1
      · ext y
        simp [G, SphereGeom.cross, cross_apply]
      · ext y
        simp [cp, q1, q2, u, v, e, SphereGeom.cross, cross_apply,
          smul_eq_mul]
        ring
    · convert ((hA 0).mul (hB 1)).sub ((hA 1).mul (hB 0)) using 1
      · ext y
        simp [G, SphereGeom.cross, cross_apply]
      · ext y
        simp [cp, q1, q2, u, v, e, SphereGeom.cross, cross_apply,
          smul_eq_mul]
        ring
  have hdn : HasFDerivAt G dn x := by
    rw [← hasFDerivWithinAt_univ]
    apply hasFDerivWithinAt_euclidean.mpr
    intro i
    have hi : HasFDerivAt (fun y => G y i) ((e i).comp dn) x := by
      apply ((ContinuousLinearMap.proj i).hasFDerivAt.comp x hcoords).congr_fderiv
      ext y
      simp [cp, dn, e, smul_eq_mul]
      ring
    exact hi.hasFDerivWithinAt
  have normCalc (F : Type 0) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      (g : E3 → F) (g' : E3 →L[ℝ] F) (hg : HasFDerivAt g g' x) (hg0 : g x ≠ 0) :
      HasFDerivAt (fun y => ‖g y‖)
        ((1 / (2 * ‖g x‖)) • ((2 • innerSL ℝ (g x)).comp g')) x := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm] using!
      hg.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hg0))
  let dnrm : E3 →L[ℝ] ℝ := (1 / (2 * N)) • ((2 • innerSL ℝ n).comp dn)
  have hnorm : HasFDerivAt (fun y => ‖G y‖) dnrm x := normCalc E3 G dn hdn hcross
  let da : E3 →L[ℝ] ℝ := -(N ^ 2)⁻¹ • dnrm
  have hda : HasFDerivAt (fun y => (‖G y‖)⁻¹) da x := by
    apply ((hasDerivAt_inv hNne).comp_hasFDerivAt x hnorm).congr_fderiv
    ext y
    simp [da, neg_smul]
  let dp : E3 →L[ℝ] E3 := N⁻¹ • dn + da.smulRight n
  have hdp : HasFDerivAt (fun y => unitDir (G y)) dp x := by
    simpa only [unitDir, dp] using! hda.smul hdn
  let D : E3 →L[ℝ] E3 := r • dp + (e 2).smulRight p
  have hD : HasFDerivAt Φ D x := by
    simpa only [Φ, G, D, r, p, N, n, u, v, unitDir] using! (he 2).smul hdp
  have hda2 : da (EuclideanSpace.single 2 1) = 0 := by
    simp [da, dnrm, dn, e, EuclideanSpace.single_apply]
  have hdetFinal : |LinearMap.det D.toLinearMap| =
      r ^ 2 * |inner ℝ p τ1| * |inner ℝ p τ2| /
        Real.sin (Real.arccos (inner ℝ u v)) :=
    HardSphereB5.SphericalCrofton.Aux.Endpoint.actual_radial_jacobian_det_formula
      u v τ1 τ2 r da hu hv hcross hda2
  change HasFDerivAt Φ (fderiv ℝ Φ x) x ∧
    |LinearMap.det (fderiv ℝ Φ x).toLinearMap| =
      r ^ 2 * |inner ℝ p τ1| * |inner ℝ p τ2| /
        Real.sin (Real.arccos (inner ℝ u v))
  rw [hD.fderiv]
  exact ⟨hD, hdetFinal⟩

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_actual_radial_jacobian
