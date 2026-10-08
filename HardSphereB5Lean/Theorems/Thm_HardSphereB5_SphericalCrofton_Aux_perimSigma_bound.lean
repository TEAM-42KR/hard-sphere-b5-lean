import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_perimSigma_bound
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.perimSigma_bound :
    ∀ (D : Pt) (hD : D ∈ LamC), 0 ≤ perim (SigmaD D) ∧ perim (SigmaD D) ≤ 4 * Real.pi :=
  @proof_HardSphereB5_SphericalCrofton_Aux_perimSigma_bound
