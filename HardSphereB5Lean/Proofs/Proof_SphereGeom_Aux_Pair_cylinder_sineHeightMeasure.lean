import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_cylinder
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_inner
set_option autoImplicit false
open MeasureTheory SphereGeom
theorem proof_SphereGeom_Aux_Pair_cylinder_sineHeightMeasure :
    (((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)).prod
      ((volume : Measure ℝ).restrict (Set.Ico 0 (2 * Real.pi)))).map
        (fun x : ℝ × ℝ => Real.sqrt (1-x.1^2) * Real.sin x.2) =
    ENNReal.ofReal (2 * Real.pi) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1) := by
  let e : Fin 3 → E3 := ![WithLp.toLp 2 ![-1,0,0], WithLp.toLp 2 ![0,0,1], WithLp.toLp 2 ![0,1,0]]
  have he : Orthonormal ℝ e := by
    apply orthonormal_iff_ite.mpr
    intro i j
    simp only [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;> norm_num [e, Fin.sum_univ_succ]
  let c : ℝ × ℝ → E3 := fun x => (Real.sqrt (1-x.1^2) * Real.cos x.2) • e 0 +
    (Real.sqrt (1-x.1^2) * Real.sin x.2) • e 1 + x.1 • e 2
  have hc : Measurable c := by dsimp [c]; fun_prop
  have hi : Measurable (fun u : E3 => inner ℝ (e 1) u) := by fun_prop
  have hcomp : (fun u : E3 => inner ℝ (e 1) u) ∘ c =
      (fun x : ℝ × ℝ => Real.sqrt (1-x.1^2) * Real.sin x.2) := by
    funext x
    simp [Function.comp_def, c, e, PiLp.inner_apply, Fin.sum_univ_succ]
  have h := dOmega_map_inner (e 1) (he.norm_eq_one 1)
  rw [dOmega_map_cylinder e he, Measure.map_map hi hc, hcomp] at h
  simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using h
