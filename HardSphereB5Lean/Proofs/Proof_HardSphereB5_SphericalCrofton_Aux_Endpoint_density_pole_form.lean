import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_cross_norm_sq
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_density_pole_form (u v τ1 τ2 : Pt) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hs : 0 < Real.sin (arccos (inner ℝ u v))) : santaloDens u v τ1 τ2 = |inner ℝ (unitDir (cross u v)) τ1| * |inner ℝ (unitDir (cross u v)) τ2| / Real.sin (arccos (inner ℝ u v)) := by
  have hn2 : ‖cross u v‖ ^ 2 = 1 - inner ℝ u v ^ 2 := by
    simpa [hu, hv] using SphereGeom.Aux.Santalo.cross_norm_sq u v
  have hn : ‖cross u v‖ = Real.sin (arccos (inner ℝ u v)) := by
    rw [Real.sin_arccos, ← hn2, Real.sqrt_sq (norm_nonneg _)]
  simp only [santaloDens, unitDir, inner_smul_left, hn]
  simp only [starRingEnd_apply, star_trivial]
  rw [abs_mul, abs_mul, abs_inv, abs_of_pos hs]
  field_simp [ne_of_gt hs]
  <;> ring
