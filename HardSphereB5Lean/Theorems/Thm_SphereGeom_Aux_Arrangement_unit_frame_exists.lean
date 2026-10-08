import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Arrangement_unit_frame_exists
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open HardSphereB5.Lean (Pt)
open scoped Classical

theorem SphereGeom.Aux.Arrangement.unit_frame_exists :
    ∀ (n : Pt) (hn : ‖n‖ = 1), ∃ e1 e2 : Pt, Orthonormal ℝ ![e1, e2, n] :=
  @proof_SphereGeom_Aux_Arrangement_unit_frame_exists
