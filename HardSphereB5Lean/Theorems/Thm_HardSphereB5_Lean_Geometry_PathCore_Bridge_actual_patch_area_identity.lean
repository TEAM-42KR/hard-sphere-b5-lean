import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_actual_patch_area_identity
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.Bridge.actual_patch_area_identity :
    ∀ {c:Fin 4→Pt} {X Y s:ℝ} (hc:IsPathConfig c X Y s) (hP:0<P4poly X Y s) (i:Fin 4), pArea c i Finset.univ=2*π-
      (∑l:Fin 4,if l≠i then gammaA c i (oth1 i l) (oth2 i l) else 0)-
      (1/2)*(∑j:Fin 4,if j≠i then dist (c i) (c j)*ell c i j else 0) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_actual_patch_area_identity
