import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_actual_patch_moment_identity
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.Bridge.actual_patch_moment_identity :
    ∀ {c:Fin 4→Pt} {X Y s:ℝ} (hc:IsPathConfig c X Y s) (hP:0<P4poly X Y s) (i:Fin 4), pMoment c i Finset.univ=
      (1/2:ℝ) • (∑j:Fin 4,if j≠i then
        ((1-q c i j/4)/√(q c i j)*ell c i j) • (c j-c i) else 0)+
      (∑l:Fin 4,if l≠i then
        let j:=oth1 i l
        let k:=oth2 i l
        let v:=c j-c i
        let w:=c k-c i
        let z:=c l-c i
        let ε:=Real.sign (det3 v w z)
        let u:=faceCircRel c i j k+(ε*(2*√(Qf c i j k)/Deltaf c i j k)) • cross v w
        (ε/4) • cross (v-w) u
        else 0) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_actual_patch_moment_identity
