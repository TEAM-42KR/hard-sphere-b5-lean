import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_dOmega_eq_three_smul_map_radial
set_option autoImplicit false
open MeasureTheory Real SphereGeom
noncomputable section

theorem proof_SphereGeom_Aux_SupportCircles_cone_frontier_null (C : Set E3) (hC : Convex ℝ C) (hcone : ∀ r : ℝ, 0 < r → (fun x : E3 => r • x) ⁻¹' C = C) : dOmega (frontier C) = 0 := by
  have hfr (r : ℝ) (hr : 0 < r) : (fun x : E3 => r • x) ⁻¹' frontier C = frontier C := by
    let e : E3 ≃ₜ E3 := Homeomorph.smulOfNeZero r (ne_of_gt hr)
    change e ⁻¹' frontier C = frontier C
    rw [e.preimage_frontier]
    have hh : e ⁻¹' C = C := hcone r hr
    rw [hh]
  have hm : Measurable (fun x : E3 => ‖x‖⁻¹ • x) := continuous_norm.measurable.inv.smul measurable_id
  have hsub : (fun x : E3 => ‖x‖⁻¹ • x) ⁻¹' frontier C ⊆ frontier C ∪ {(0 : E3)} := by
    intro x hx
    by_cases hz : x = 0
    · right; exact hz
    · left
      have hmem : x ∈ (fun y : E3 => ‖x‖⁻¹ • y) ⁻¹' frontier C := hx
      rw [hfr (‖x‖⁻¹) (inv_pos.mpr (norm_pos_iff.mpr hz))] at hmem
      exact hmem
  have hnull : volume ((fun x : E3 => ‖x‖⁻¹ • x) ⁻¹' frontier C) = 0 :=
    measure_mono_null hsub (measure_union_null (hC.addHaar_frontier volume) (measure_singleton (0 : E3)))
  rw [SphereGeom.Aux.Crofton.dOmega_eq_three_smul_map_radial, Measure.smul_apply,
    Measure.map_apply hm isClosed_frontier.measurableSet,
    Measure.restrict_apply (isClosed_frontier.measurableSet.preimage hm)]
  rw [measure_mono_null Set.inter_subset_left hnull]
  simp

