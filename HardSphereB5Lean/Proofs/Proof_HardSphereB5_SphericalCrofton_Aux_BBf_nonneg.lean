import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_phiK_nonneg
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
private theorem cut_nonneg (f : Kern) (δ : ℝ) (hδ : 0 ≤ δ) : 0 ≤ cutKern f δ := by
  unfold cutKern
  split_ifs with h
  · exact phiK_nonneg f δ hδ (le_of_lt h)
  · rfl
private theorem dens_nonneg (u v τ1 τ2 : Pt) : 0 ≤ santaloDens u v τ1 τ2 := by
  unfold santaloDens
  apply div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact pow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩) 3
theorem proof_HardSphereB5_SphericalCrofton_Aux_BBf_nonneg (f : Kern) (D : Pt) : 0 ≤ BBf f D := by
  unfold BBf
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro u
  apply integral_nonneg
  intro v
  exact mul_nonneg (cut_nonneg f _ (Real.arccos_nonneg _)) (dens_nonneg _ _ _ _)
