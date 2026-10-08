import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_sigma_support
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.sigma_support :
    ∀ (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D), (Rc ‖D‖ ‖D - e‖ < 1 → 0 < sArea (SigmaD D) ∧ ∃ V W, V ≠ W ∧ vertsD D = {V, W}) ∧
      (Rc ‖D‖ ‖D - e‖ = 1 → ∃ V, SigmaD D = {V}) ∧
      (1 < Rc ‖D‖ ‖D - e‖ → SigmaD D = ∅) :=
  @proof_HardSphereB5_SphericalCrofton_sigma_support
