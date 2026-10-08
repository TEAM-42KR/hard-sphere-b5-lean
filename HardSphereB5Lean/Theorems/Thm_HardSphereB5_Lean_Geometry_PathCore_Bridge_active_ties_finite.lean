import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_active_ties_finite
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_BulkMatching
set_option autoImplicit false
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped RealInnerProductSpace

theorem HardSphereB5.Lean.Geometry.PathCore.Bridge.active_ties_finite :
    ∀ {c : Fin 4 → E3} {X Y s : ℝ} (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s) (P : Profile) (i : Fin 4) (o : Fin 3 → Fin 4) (hm : BulkMatching P c i o), (tieAzimuth P).Finite :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_active_ties_finite
