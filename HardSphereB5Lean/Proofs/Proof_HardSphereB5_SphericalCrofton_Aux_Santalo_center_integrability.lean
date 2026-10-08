import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_vertex_integrability
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_Bf_uniform_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Bf_aestronglyMeasurable
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_center_integrability (f : Kern) :
    IntegrableOn (fun D => if offAxis D ∧ Rc ‖D‖ ‖D - e‖ < 1 then
      2 * Pprim f (min (deltaV D) (Real.pi / 3)) else 0) LamC volume ∧
    IntegrableOn (Bf f) LamC volume := by
  constructor
  · exact vertex_integrability f
  · have hfin : (volume : Measure Pt) LamC < ⊤ :=
      lt_of_le_of_lt (measure_mono Set.inter_subset_left)
        (isCompact_closedBall (0 : Pt) 1).measure_lt_top
    have hs : MeasurableSet LamC :=
      (Metric.isClosed_closedBall.inter Metric.isClosed_closedBall).measurableSet
    exact IntegrableOn.of_bound hfin (HardSphereB5.SphericalCrofton.Aux.Bf_aestronglyMeasurable f)
      (16 * Real.pi ^ 2) (ae_restrict_of_forall_mem hs (Bf_uniform_bound f))
