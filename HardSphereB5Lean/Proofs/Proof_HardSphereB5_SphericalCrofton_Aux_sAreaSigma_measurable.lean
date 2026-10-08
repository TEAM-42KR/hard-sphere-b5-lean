import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_measurable : Measurable (fun D : Pt => sArea (SigmaD D)) := by
  letI : IsFiniteMeasure dOmega := ⟨by
    change dOmega Set.univ < ⊤
    rw [dOmega, sphereMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  have hLam : IsClosed LamC := Metric.isClosed_closedBall.inter Metric.isClosed_closedBall
  let G : Set (Pt × Pt) := {z | z.2 ∈ SigmaD z.1}
  have hG : MeasurableSet G := by
    have hs : IsClosed {z : Pt × Pt | ‖z.2‖ = (1 : ℝ)} :=
      isClosed_eq continuous_snd.norm continuous_const
    have hl : IsClosed {z : Pt × Pt | z.1 + z.2 ∈ LamC} :=
      hLam.preimage (continuous_fst.add continuous_snd)
    exact (hs.inter hl).measurableSet
  change Measurable (fun D : Pt => (dOmega (Prod.mk D ⁻¹' G)).toReal)
  exact (measurable_measure_prodMk_left (ν := dOmega) hG).ennreal_toReal

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_measurable
