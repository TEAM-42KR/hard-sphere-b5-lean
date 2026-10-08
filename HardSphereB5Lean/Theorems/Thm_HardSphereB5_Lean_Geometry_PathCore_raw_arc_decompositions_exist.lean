import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_raw_arc_decompositions_exist
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.raw_arc_decompositions_exist :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0), Nonempty (∀ e : PairIndex, PairArcDecomposition c e.1.1 e.1.2) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_raw_arc_decompositions_exist
