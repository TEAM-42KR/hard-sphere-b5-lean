import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_measurable_kernels
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.measurable_kernels :
    ∀ (f : Kern) (D : Pt), Measurable (Function.uncurry (abKernel f D)) ∧ Measurable (Function.uncurry (bKernel f D)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_measurable_kernels
