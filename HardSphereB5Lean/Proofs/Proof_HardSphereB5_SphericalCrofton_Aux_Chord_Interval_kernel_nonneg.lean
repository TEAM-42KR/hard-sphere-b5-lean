import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_kernel_nonneg (f : Kern) (L : ℝ) (h0 : 0 ≤ L) : 0 ≤ kK f L := by
  have hcut : 0 ≤ min L (π / 3) := le_min h0 (by positivity)
  unfold kK
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg hcut
  intro t ht
  have htL : t ≤ L := le_trans ht.2 (min_le_left _ _)
  have htcut : t ≤ π / 3 := le_trans ht.2 (min_le_right _ _)
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [Real.pi_pos])
  have hw : 0 ≤ wK f (Real.cos t) := by
    cases f
    · simp [wK]
    · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], by linarith [Real.pi_pos]⟩
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr htL) hw) hs
