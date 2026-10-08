import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_capCorner_gamma
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_tailAngle
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section

theorem SolidGeom.CapPolar.capCorner_gamma :
    ∀ (c : Fin 4 → SphereGeom.E3) (i j k : Fin 4)
    (u : SphereGeom.E3) (hu : ‖u‖=1)
    (hj : ‖u-(c j-c i)‖=1) (hk : ‖u-(c k-c i)‖=1)
    (hpos : 0 < inner ℝ u (SphereGeom.cross (c j-c i) (c k-c i))), SolidGeom.CapPolar.capCorner u (c j-c i) (c k-c i)=HardSphereB5.Lean.Geometry.PathCore.gammaA c i j k :=
  @proof_SolidGeom_CapPolar_capCorner_gamma
