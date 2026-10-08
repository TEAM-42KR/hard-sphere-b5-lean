import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_cross_arc_by_parts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_center_integrability
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_inactive_cross_zero
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_AB_chain (f : Kern) : ABint f = Ic f + frakB f := by
  rcases center_integrability f with ⟨hI, hB⟩
  unfold ABint Ic frakB
  rw [← integral_add hI hB]
  apply integral_congr_ae
  have hLam : MeasurableSet LamC := by unfold LamC; exact measurableSet_closedBall.inter measurableSet_closedBall
  filter_upwards [ae_restrict_mem hLam] with D hD
  by_cases hgood : offAxis D ∧ Rc ‖D‖ ‖D - e‖ < 1
  · rw [if_pos hgood]
    exact HardSphereB5.SphericalCrofton.cross_arc_by_parts f D hD hgood.1 hgood.2
  · rcases inactive_cross_zero f D hD hgood with ⟨hAB, hB⟩
    simp [hgood, hAB, hB]
