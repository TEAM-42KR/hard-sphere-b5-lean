import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_near_as_spherical (f : Kern) : Jnear f = ∫ D in LamC, Ff f (SigmaD D) := by
  have huval : MeasurableEmbedding (fun u : Metric.sphere (0 : Pt) 1 => (u : Pt)) :=
    ((Metric.isClosed_sphere : IsClosed (Metric.sphere (0 : Pt) 1)).isClosedEmbedding_subtypeVal).measurableEmbedding
  have htrans (D : Pt) : MeasurableEmbedding (fun u : Metric.sphere (0 : Pt) 1 => D + (u : Pt)) :=
    (Homeomorph.addLeft D).toMeasurableEquiv.measurableEmbedding.comp huval
  unfold Jnear Ff
  apply setIntegral_congr_fun (by unfold LamC; measurability)
  intro D hD
  simp only [sphereMeasure]
  rw [(htrans D).setIntegral_map]
  simp only [dOmega, sphereMeasure, zero_add]
  rw [huval.setIntegral_map]
  have hsets : (fun u : Metric.sphere (0 : Pt) 1 => D + (u : Pt)) ⁻¹' LamC =
      (fun u : Metric.sphere (0 : Pt) 1 => (u : Pt)) ⁻¹' SigmaD D := by
    ext u
    simp only [Set.mem_preimage, SigmaD, Set.mem_setOf_eq]
    have hu : ‖(u : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using u.property
    simp [hu]
  rw [hsets]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [(htrans D).setIntegral_map, huval.setIntegral_map, hsets]
  apply integral_congr_ae
  filter_upwards [] with v
  have hu : ‖(u : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using u.property
  have hv : ‖(v : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using v.property
  have hdist : dist (D + (u : Pt)) (D + (v : Pt)) ≤ 1 ↔ (1 / 2 : ℝ) ≤ inner ℝ (u : Pt) (v : Pt) := by
    rw [dist_add_left, dist_eq_norm]
    have hh : ‖(u : Pt) - (v : Pt)‖ ^ 2 = 2 - 2 * inner ℝ (u : Pt) (v : Pt) := by
      rw [norm_sub_sq_real, hu, hv]; ring
    constructor
    · intro h
      have hs : ‖(u : Pt) - (v : Pt)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ((u : Pt) - (v : Pt))]
      nlinarith
    · intro h
      nlinarith [norm_nonneg ((u : Pt) - (v : Pt))]
  simp only [add_sub_cancel_left, hdist]

