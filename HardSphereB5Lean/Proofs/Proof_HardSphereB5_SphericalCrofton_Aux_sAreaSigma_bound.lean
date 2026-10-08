import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_bound (D : Pt) :
    0 ≤ sArea (SigmaD D) ∧ sArea (SigmaD D) ≤ 4 * Real.pi := by
  have hmass : dOmega Set.univ = ENNReal.ofReal (4 * Real.pi) := sphereMeasure_univ 0
  have htop : dOmega Set.univ ≠ ⊤ := by rw [hmass]; exact ENNReal.ofReal_ne_top
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hle := ENNReal.toReal_mono htop (measure_mono (Set.subset_univ (SigmaD D)))
  simpa only [sArea, hmass, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 4 * Real.pi)] using hle

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_bound
