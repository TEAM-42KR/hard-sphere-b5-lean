import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_alignedCap_exists
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_AlignedCap
set_option autoImplicit false
noncomputable section
open SphereGeom SolidGeom.CapPolar

theorem SolidGeom.CapPolar.alignedCap_exists :
    ∀ (P : SolidGeom.CapPolar.Profile)
    (hor : SphereGeom.cross (P.e 2) (P.e 0)=P.e 1) (j : Fin 3), Nonempty (SolidGeom.CapPolar.AlignedCap P j) :=
  @proof_SolidGeom_CapPolar_alignedCap_exists
