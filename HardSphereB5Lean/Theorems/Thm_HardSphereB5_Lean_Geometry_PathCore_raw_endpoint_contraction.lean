import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_contraction
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.raw_endpoint_contraction :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0)
  (D : ∀ e : PairIndex, PairArcDecomposition c e.1.1 e.1.2), rawEndpointSum c D = ((∑ l, (nRet c l : ℝ)*√(Qface c l)) -
    (if 0<P4poly X Y s then √(Hpoly X Y s) else 0)) / 2 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_contraction
