import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Cylinder_standard_map
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_linearIsometryEquiv
set_option autoImplicit false

open MeasureTheory SphereGeom
set_option maxHeartbeats 800000

theorem proof_SphereGeom_dOmega_map_cylinder (e : Fin 3 → E3) (he : Orthonormal ℝ e) :
    dOmega =
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (2 * Real.pi))).map
        (fun x : ℝ × ℝ =>
          (Real.sqrt (1 - x.1 ^ 2) * Real.cos x.2) • e 0 +
          (Real.sqrt (1 - x.1 ^ 2) * Real.sin x.2) • e 1 + x.1 • e 2) := by
  classical
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range e) := by
    apply Eq.ge
    apply he.linearIndependent.span_eq_top_of_card_eq_finrank
    simp [E3]
  let b : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk he hspan
  let R : E3 ≃ₗᵢ[ℝ] E3 := b.repr.symm
  let f : (ℝ × ℝ) → E3 := fun x => WithLp.toLp 2
    ![Real.sqrt (1-x.1^2) * Real.cos x.2,
      Real.sqrt (1-x.1^2) * Real.sin x.2, x.1]
  let μ : Measure (ℝ × ℝ) := (volume : Measure (ℝ × ℝ)).restrict
    (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (2 * Real.pi))
  have hb (i : Fin 3) : b i = e i := by
    simp [b]
  have hframe (x : ℝ × ℝ) : R (f x) =
      (Real.sqrt (1 - x.1 ^ 2) * Real.cos x.2) • e 0 +
      (Real.sqrt (1 - x.1 ^ 2) * Real.sin x.2) • e 1 + x.1 • e 2 := by
    dsimp only [R]
    rw [← b.sum_repr_symm]
    simp [Fin.sum_univ_succ, hb, f, add_assoc]
  have hf : Measurable f := by
    apply Continuous.measurable
    fun_prop
  calc
    dOmega = dOmega.map R := (dOmega_map_linearIsometryEquiv R).symm
    _ = (μ.map f).map R := by rw [SphereGeom.Aux.Cylinder.standard_map]
    _ = μ.map (R ∘ f) := Measure.map_map R.continuous.measurable hf
    _ = _ := by
      congr 1
      funext x
      exact hframe x
