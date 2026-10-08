import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_ABf_joint_kernel_measurable
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.ABf_joint_kernel_measurable :
    ∀ (f : Kern), Measurable
    (fun z : Pt × (Pt × Pt) =>
      if z.2.1 ∈ arcA z.1 ∧ z.2.2 ∈ arcB z.1 then
        cutKern f (arccos (inner ℝ z.2.1 z.2.2)) *
          santaloDens z.2.1 z.2.2 (tanA z.1 z.2.1) (tanB z.1 z.2.2) else 0) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_ABf_joint_kernel_measurable
