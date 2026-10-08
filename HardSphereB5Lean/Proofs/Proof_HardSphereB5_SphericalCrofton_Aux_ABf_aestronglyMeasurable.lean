import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_cross_arc_parameter_integral_aestronglyMeasurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_ABf_joint_kernel_measurable
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
open HardSphereB5.SphericalCrofton.Aux
noncomputable section
set_option maxHeartbeats 600000
theorem proof_HardSphereB5_SphericalCrofton_Aux_ABf_aestronglyMeasurable (f : Kern) : AEStronglyMeasurable (ABf f) (volume.restrict LamC) := by
  let K : Pt × (Pt × Pt) → ℝ := fun z =>
    if z.2.1 ∈ arcA z.1 ∧ z.2.2 ∈ arcB z.1 then cutKern f (arccos (inner ℝ z.2.1 z.2.2)) * santaloDens z.2.1 z.2.2 (tanA z.1 z.2.1) (tanB z.1 z.2.2) else 0
  have hm := cross_arc_parameter_integral_aestronglyMeasurable K (ABf_joint_kernel_measurable f)
  apply hm.congr
  filter_upwards [] with D
  have hAset : MeasurableSet {z : Pt × Pt | z.2 ∈ arcA z.1} := by
    have heq : {z : Pt × Pt | z.2 ∈ arcA z.1} =
        {z : Pt × Pt | z.1 ≠ 0 ∧ ‖z.2‖ = 1 ∧ ‖z.1 + z.2‖ ≤ 1 ∧
          dist (z.1 + z.2) e ≤ 1 ∧ ‖z.1 + z.2‖ = 1} := by
      ext z
      by_cases h : z.1 = 0 <;> simp [arcA, SigmaD, LamC, h, and_assoc]
    rw [heq]
    measurability
  have hBset : MeasurableSet {z : Pt × Pt | z.2 ∈ arcB z.1} := by
    have heq : {z : Pt × Pt | z.2 ∈ arcB z.1} =
        {z : Pt × Pt | z.1 ≠ e ∧ ‖z.2‖ = 1 ∧ ‖z.1 + z.2‖ ≤ 1 ∧
          dist (z.1 + z.2) e ≤ 1 ∧ dist (z.1 + z.2) e = 1} := by
      ext z
      by_cases h : z.1 = e <;> simp [arcB, SigmaD, LamC, h, and_assoc]
    rw [heq]
    measurability

  have hA : MeasurableSet (arcA D) := hAset.preimage (measurable_const.prodMk measurable_id)
  have hB : MeasurableSet (arcB D) := hBset.preimage (measurable_const.prodMk measurable_id)
  unfold ABf
  apply setIntegral_congr_fun hA
  intro u hu
  apply setIntegral_congr_fun hB
  intro v hv
  simp [K,hu,hv]
