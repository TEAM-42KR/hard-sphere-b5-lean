import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Cap_frontier_slice
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Cap.frontier_slice :
    ∀ (n : Pt) (hn : ‖n‖ = 1) (h : ℝ) (h0 : 0 < h) (h1 : h < 1), sFrontier (cap n h) = {u : Pt | ‖u‖ = 1 ∧ inner ℝ n u = h} :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Cap_frontier_slice
