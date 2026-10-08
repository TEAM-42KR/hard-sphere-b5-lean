import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_volume
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.raw_endpoint_volume :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0)
  (D : ∀ e : PairIndex, PairArcDecomposition c e.1.1 e.1.2), vol c Finset.univ = 8*π/3 - (1/3)*∑ l, (nRet c l : ℝ)*sigmaF c l -
    (1/2)*∑ i, ∑ j, (if i<j then g (dist (c i) (c j))*ell c i j else 0) + rawEndpointSum c D / 6 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_volume
