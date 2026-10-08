import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false

open HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Matrix

theorem proof_HardSphereB5_SphericalCrofton_Aux_Flat_existsAxialRotation (t : ℝ) :
    ∃ R : Pt ≃ₗᵢ[ℝ] Pt, IsAxialRotation R ∧
      ∀ a b c : ℝ, R (a • e1 + b • e2 + c • e) =
        (a * Real.cos t - b * Real.sin t) • e1 +
        (a * Real.sin t + b * Real.cos t) • e2 + c • e := by
  classical
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    !![1, 0, 0; 0, Real.cos t, -Real.sin t; 0, Real.sin t, Real.cos t]
  let L : Pt →ₗ[ℝ] Pt := Matrix.toEuclideanLin M
  have hdet : LinearMap.det L = 1 := by
    dsimp only [L]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
    simp [M, Matrix.det_fin_three]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hL (x : Pt) : L x =
      WithLp.toLp 2 ![x 0, Real.cos t * x 1 - Real.sin t * x 2,
        Real.sin t * x 1 + Real.cos t * x 2] := by
    ext i
    fin_cases i <;>
      simp [L, M, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] <;> ring
  have hnorm (x : Pt) : ‖L x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, hL]
    simp [Fin.sum_univ_succ]
    nlinarith [congrArg (fun z : ℝ => z * (x 1) ^ 2) (Real.sin_sq_add_cos_sq t),
      congrArg (fun z : ℝ => z * (x 2) ^ 2) (Real.sin_sq_add_cos_sq t)]
  have hbij : Function.Bijective L := by
    apply (Module.End.isUnit_iff L).mp
    apply (LinearMap.isUnit_iff_isUnit_det L).mpr
    rw [hdet]
    exact isUnit_one
  let R : Pt ≃ₗᵢ[ℝ] Pt :=
    { LinearEquiv.ofBijective L hbij with norm_map' := hnorm }
  refine ⟨R, ⟨?_, ?_⟩, ?_⟩
  · change L e = e
    rw [hL]
    ext i
    fin_cases i <;> simp [e]
  · exact hdet
  · intro a b c
    change L (a • e1 + b • e2 + c • e) = _
    rw [hL]
    ext i
    fin_cases i <;> simp [e1, e2, e] <;> ring
