import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
set_option maxHeartbeats 1200000

theorem proof_SphereGeom_Aux_Cylinder_jacobian (x : Fin 3 → ℝ) (hx : -1 < x 1 ∧ x 1 < 1) :
    let f : (Fin 3 → ℝ) → Fin 3 → ℝ := fun y =>
      ![y 0 * Real.sqrt (1 - (y 1)^2) * Real.cos (y 2),
        y 0 * Real.sqrt (1 - (y 1)^2) * Real.sin (y 2), y 0 * y 1]
    (Matrix.det (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
      (fderiv ℝ f x).toLinearMap)) = -(x 0)^2 := by
  dsimp only
  have hpos : 0 < 1 - (x 1)^2 := by nlinarith [hx.1, hx.2]
  have hspos : 0 < Real.sqrt (1 - (x 1)^2) := Real.sqrt_pos.2 hpos
  have hssq := Real.sq_sqrt (le_of_lt hpos)
  let e : Fin 3 → ((Fin 3 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
  have hr := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x
  have hz := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 x
  have ht := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 x
  have hs := ((hasFDerivAt_const (1 : ℝ) x).sub (hz.mul hz)).sqrt
    (by simpa [pow_two] using ne_of_gt hpos)
  let s := Real.sqrt (1 - (x 1)^2)
  let ds : (Fin 3 → ℝ) →L[ℝ] ℝ := (1 / (2 * s)) • (-(x 1 • e 1 + x 1 • e 1))
  let drs : (Fin 3 → ℝ) →L[ℝ] ℝ := x 0 • ds + s • e 0
  let d : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi
    ![(x 0 * s) • (-Real.sin (x 2) • e 2) + Real.cos (x 2) • drs,
      (x 0 * s) • (Real.cos (x 2) • e 2) + Real.sin (x 2) • drs,
      x 0 • e 1 + x 1 • e 0]
  have hd : HasFDerivAt (fun y : Fin 3 → ℝ =>
      ![y 0 * Real.sqrt (1 - (y 1)^2) * Real.cos (y 2),
        y 0 * Real.sqrt (1 - (y 1)^2) * Real.sin (y 2), y 0 * y 1]) d x := by
    apply hasFDerivAt_pi.2
    intro i
    fin_cases i
    · simpa [d, drs, ds, s, e, pow_two] using! (hr.mul hs).mul ht.cos
    · simpa [d, drs, ds, s, e, pow_two] using! (hr.mul hs).mul ht.sin
    · simpa [d, e] using! hr.mul hz
  rw [hd.fderiv]
  rw [Matrix.det_fin_three]
  simp [LinearMap.toMatrix_apply, Pi.basisFun_apply, d, drs, ds, e, s]
  field_simp [hspos.ne']
  have hcs : Real.sqrt (1 - (x 1)^2)^2 + (x 1)^2 = 1 := by linarith
  calc
    _ = -((x 0)^2 * 2) *
        (Real.sqrt (1 - (x 1)^2)^2 + (x 1)^2) *
        (Real.sin (x 2)^2 + Real.cos (x 2)^2) := by ring
    _ = _ := by rw [hcs, Real.sin_sq_add_cos_sq]; ring
