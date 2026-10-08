import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_phiK_nonneg
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_cutKern_arccos_bound (f : Kern) (x : ℝ) :
    0 ≤ cutKern f (Real.arccos x) ∧ cutKern f (Real.arccos x) ≤ 6 := by
  by_cases hcut : Real.arccos x < Real.pi / 3
  · simp only [cutKern, if_pos hcut]
    refine ⟨phiK_nonneg f _ (Real.arccos_nonneg x) hcut.le, ?_⟩
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
    have hp := Real.pi_lt_four
    have hp0 := Real.pi_pos
    have ha0 := Real.arccos_nonneg x
    cases f <;> simp only [phiK]
    · nlinarith [Real.neg_one_le_sin (Real.arccos x)]
    · nlinarith [Real.neg_one_le_sin (2 * Real.arccos x)]
  · simp [cutKern, hcut]

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_cutKern_arccos_bound
