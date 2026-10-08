import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_measurable
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.sAreaSigma_measurable :
    Measurable (fun D : Pt => sArea (SigmaD D)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_sAreaSigma_measurable
