import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_actual_radial_jacobian
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_density_pole_form
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_cross_norm_sq
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
open Filter Topology

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_det (D : Pt) (C : CircleEndpointAtlas) (hC : IsCircleEndpointAtlas D C)
    (x : Pt) (hx : x ∈ atlasRadialSource C) :
    |(fderiv ℝ (atlasRadial C) x).det| = (x 2)^2 * atlasSpeed C (x 0) *
      atlasSpeed C (x 1) * pairDens D (atlasPair C x) := by
  classical
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
  let u : Pt := atlasGamma C (x 0)
  let v : Pt := atlasGamma C (x 1)
  have hu : ‖u‖ = 1 := hC.unit _ hx.1
  have hv : ‖v‖ = 1 := hC.unit _ hx.2.1
  have hc : cross u v ≠ 0 := hx.2.2.2
  have hs : 0 < Real.sin (arccos (inner ℝ u v)) := by
    rw [Real.sin_arccos]
    apply Real.sqrt_pos.mpr
    have heq := SphereGeom.Aux.Santalo.cross_norm_sq u v
    rw [hu, hv] at heq
    have hp := sq_pos_of_pos (norm_pos_iff.mpr hc)
    nlinarith
  obtain ⟨k, hk, hks⟩ := hC.tangent _ hx.1
  obtain ⟨l, hl, hls⟩ := hC.tangent _ hx.2.1
  have hdet := (actual_radial_jacobian (atlasGamma C) (atlasGamma C)
    (deriv (atlasGamma C) (x 0)) (deriv (atlasGamma C) (x 1)) x
    (hgder _ hx.1) (hgder _ hx.2.1) hu hv hc).2
  change |(fderiv ℝ (atlasRadial C) x).det| = _ at hdet
  rw [hdet]
  change _ = (x 2)^2 * atlasSpeed C (x 0) * atlasSpeed C (x 1) *
    santaloDens u v (boundaryTau D u) (boundaryTau D v)
  rw [density_pole_form u v (boundaryTau D u) (boundaryTau D v) hu hv hs]
  rw [hk, hl, inner_smul_right, inner_smul_right, abs_mul, abs_mul, hks, hls]
  ring
