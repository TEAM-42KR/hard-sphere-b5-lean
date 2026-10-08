import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_profile_patch_measure
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_BulkMatching
set_option autoImplicit false
noncomputable section
open MeasureTheory

theorem HardSphereB5.Lean.Geometry.PathCore.Bridge.profile_patch_measure :
    ∀ {P : SolidGeom.CapPolar.Profile} {c : Fin 4 → SphereGeom.E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : SolidGeom.CapPolar.BulkMatching P c i o), HardSphereB5.Lean.Geometry.PathCore.pArea c i Finset.univ=(SphereGeom.dOmega (SolidGeom.CapPolar.caps P)).toReal ∧
      HardSphereB5.Lean.Geometry.PathCore.pMoment c i Finset.univ=
        ∫ u in SolidGeom.CapPolar.caps P, u ∂SphereGeom.dOmega :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_profile_patch_measure
