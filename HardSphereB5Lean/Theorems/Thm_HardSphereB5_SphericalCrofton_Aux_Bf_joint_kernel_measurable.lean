import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Bf_joint_kernel_measurable
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Bf_joint_kernel_measurable :
    ∀ (f : Kern), Measurable
    (fun z : Pt × (Pt × Pt) =>
      if z.2.1 ∈ arcA z.1 ∧ z.2.2 ∈ arcB z.1 then
        (if 1 / 2 < inner ℝ z.2.1 z.2.2 then
          rhoK f (inner ℝ z.2.1 z.2.2) * inner ℝ (nAv z.1) (cross z.2.1 z.2.2) *
            inner ℝ (nBv z.1) (cross z.2.1 z.2.2) else 0) /
          (√(1 - ‖z.1‖ ^ 2 / 4) * √(1 - ‖z.1 - e‖ ^ 2 / 4))
      else 0) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Bf_joint_kernel_measurable
