import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_active_patch_circle_image
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_BulkMatching
set_option autoImplicit false
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.Bridge.active_patch_circle_image :
    ∀ (P : SolidGeom.CapPolar.Profile) (c : Fin 4 → SphereGeom.E3) (i : Fin 4)
    (o : Fin 3 → Fin 4) (hm : SolidGeom.CapPolar.BulkMatching P c i o) (j : Fin 3), (fun φ => c i + SolidGeom.CapPolar.exitPoint P φ) '' SolidGeom.CapPolar.activeAzimuth P j =
      HardSphereB5.Lean.Geometry.PathCore.patch c i ∩ Metric.sphere (c (o j)) 1 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_active_patch_circle_image
