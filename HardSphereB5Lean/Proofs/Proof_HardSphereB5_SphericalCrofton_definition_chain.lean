import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_near_as_spherical
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_crofton_decomposition
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_spherical_remainder_split
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Sigma_regular_or_small
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_small_region_zero
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_integrableOn
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_perim_integrable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_AA_BB_integrable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_AB_integrable
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_definition_chain (f : Kern) : Jnear f = ECr f + Rsame f + ABint f := by
  rw [near_as_spherical]
  have hpoint (D : Pt) (hD : D ∈ LamC) :
      Ff f (SigmaD D) = (cA f * sArea (SigmaD D) - cP f * perim (SigmaD D)) +
        (AAf f D + BBf f D) + ABf f D := by
    have hCroft : Ff f (SigmaD D) = cA f * sArea (SigmaD D) -
        cP f * perim (SigmaD D) + Rf f (SigmaD D) := by
      rcases Aux.Sigma_regular_or_small D hD with hr | hs
      · exact crofton_decomposition hr f
      · obtain ⟨hF, hA, hP, hR⟩ := Aux.small_region_zero (SigmaD D) hs f
        simp [hF, hA, hP, hR]
    rw [hCroft, spherical_remainder_split f D hD]
    ring
  rw [setIntegral_congr_fun (by unfold LamC; measurability) hpoint]
  have hA := (Aux.sAreaSigma_integrableOn).const_mul (cA f)
  have hP := (Aux.perim_integrable).const_mul (cP f)
  have hSame := Aux.AA_BB_integrable f
  have hAB := Aux.AB_integrable f
  have h1 := integral_add ((hA.sub hP).add hSame) hAB
  have h2 := integral_add (hA.sub hP) hSame
  have h3 := integral_sub hA hP
  simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
  rw [h1, h2, h3, integral_const_mul, integral_const_mul]
  rfl
