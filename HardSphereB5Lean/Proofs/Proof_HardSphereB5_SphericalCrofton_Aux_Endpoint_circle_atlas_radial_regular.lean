import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_actual_radial_jacobian
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pole_orientation
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
open Filter Topology

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_regular (D : Pt) (C : CircleEndpointAtlas) (hC : IsCircleEndpointAtlas D C) :
    Measurable (atlasRadial C) ∧ Measurable (fderiv ℝ (atlasRadial C)) ∧
      Measurable (atlasPair C) ∧ MeasurableSet (atlasRadialSource C) ∧
      (∀ x ∈ atlasRadialSource C, HasFDerivWithinAt (atlasRadial C)
        (fderiv ℝ (atlasRadial C) x) (atlasRadialSource C) x) ∧
      (∀ x ∈ atlasRadialSource C,
        ‖atlasRadial C x‖⁻¹ • atlasRadial C x = pairPole (atlasPair C x)) := by
  classical
  have hgamma : Measurable (atlasGamma C) := by
    unfold atlasGamma
    apply Measurable.ite measurableSet_Iio
    · dsimp [atlasCircle, circlePt]; fun_prop
    · dsimp [atlasCircle, circlePt]; fun_prop
  have hpair : Measurable (atlasPair C) := by
    unfold atlasPair
    fun_prop
  have hradial : Measurable (atlasRadial C) := by
    unfold atlasRadial unitDir cross
    fun_prop
  have hJ : MeasurableSet (atlasInterval C) := measurableSet_Ioo.union measurableSet_Ioo
  have hs : MeasurableSet (atlasRadialSource C) := by
    have h0 : Measurable (fun x : Pt => x 0) := by fun_prop
    have h1 : Measurable (fun x : Pt => x 1) := by fun_prop
    have h2 : Measurable (fun x : Pt => x 2) := by fun_prop
    have hc : Measurable (fun x : Pt => cross (atlasGamma C (x 0)) (atlasGamma C (x 1))) := by
      unfold cross
      fun_prop
    exact (h0 hJ).inter ((h1 hJ).inter ((h2 measurableSet_Ioo).inter
      (hc (measurableSet_singleton (0 : Pt)).compl)))
  have hgder : ∀ t ∈ atlasInterval C, HasDerivAt (atlasGamma C) (deriv (atlasGamma C) t) t := by
    intro t ht
    rcases ht with ht | ht
    · have ht0 : t < 0 := by linarith [ht.2, hC.width_le 0]
      let g : ℝ → Pt := fun z => atlasCircle C 0 (z + (2 * Real.pi + 1))
      have hc : ContDiff ℝ 1 g := by dsimp [g, atlasCircle, circlePt]; fun_prop
      have hEq : atlasGamma C =ᶠ[𝓝 t] g := by
        filter_upwards [eventually_lt_nhds ht0] with z hz
        simp only [atlasGamma, if_pos hz, g]
      have hd := ((hc.differentiable (by norm_num)) t).hasDerivAt.congr_of_eventuallyEq hEq
      exact hd.differentiableAt.hasDerivAt
    · have ht0 : 0 < t := by linarith [ht.1]
      let g : ℝ → Pt := fun z => atlasCircle C 1 (z - 1)
      have hc : ContDiff ℝ 1 g := by dsimp [g, atlasCircle, circlePt]; fun_prop
      have hEq : atlasGamma C =ᶠ[𝓝 t] g := by
        filter_upwards [eventually_gt_nhds ht0] with z hz
        simp only [atlasGamma, if_neg (not_lt.mpr hz.le), g]
      have hd := ((hc.differentiable (by norm_num)) t).hasDerivAt.congr_of_eventuallyEq hEq
      exact hd.differentiableAt.hasDerivAt
  have hder : ∀ x ∈ atlasRadialSource C, HasFDerivWithinAt (atlasRadial C)
      (fderiv ℝ (atlasRadial C) x) (atlasRadialSource C) x := by
    intro x hx
    exact (actual_radial_jacobian (atlasGamma C) (atlasGamma C)
      (deriv (atlasGamma C) (x 0)) (deriv (atlasGamma C) (x 1)) x
      (hgder _ hx.1) (hgder _ hx.2.1) (hC.unit _ hx.1) (hC.unit _ hx.2.1)
      hx.2.2.2).1.hasFDerivWithinAt
  have hdir : ∀ x ∈ atlasRadialSource C,
      ‖atlasRadial C x‖⁻¹ • atlasRadial C x = pairPole (atlasPair C x) := by
    intro x hx
    have hp : ‖pairPole (atlasPair C x)‖ = 1 :=
      (pole_orientation (atlasGamma C (x 0)) (atlasGamma C (x 1))).2.2.2 hx.2.2.2
    have hn : ‖atlasRadial C x‖ = x 2 := by
      change ‖(x 2) • pairPole (atlasPair C x)‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hx.2.2.1.1, hp, mul_one]
    change ‖atlasRadial C x‖⁻¹ • ((x 2) • pairPole (atlasPair C x)) = _
    rw [hn, smul_smul, inv_mul_cancel₀ (ne_of_gt hx.2.2.1.1), one_smul]
  exact ⟨hradial, measurable_fderiv ℝ (atlasRadial C), hpair, hs, hder, hdir⟩
