import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_capCorner_pos_smul
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_tailAngle
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section

theorem SolidGeom.CapPolar.capCorner_pos_smul :
    ∀ (u n m : SphereGeom.E3) (r s : ℝ)
    (hr : 0<r) (hs : 0<s), SolidGeom.CapPolar.capCorner u (r • n) (s • m)=SolidGeom.CapPolar.capCorner u n m :=
  @proof_SolidGeom_CapPolar_capCorner_pos_smul
