import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_cutKern_arccos_bound
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_AAf_nonneg (f : Kern) (D : Pt) : 0 ≤ AAf f D := by
  have hdens (u v τ1 τ2 : Pt) : 0 ≤ santaloDens u v τ1 τ2 := by
    exact div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _)
        (Real.arccos_le_pi _)) 3)
  unfold AAf
  refine mul_nonneg (by norm_num) (integral_nonneg fun u => ?_)
  exact integral_nonneg fun v =>
    mul_nonneg (HardSphereB5.SphericalCrofton.Aux.cutKern_arccos_bound f _).1 (hdens _ _ _ _)

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_AAf_nonneg
