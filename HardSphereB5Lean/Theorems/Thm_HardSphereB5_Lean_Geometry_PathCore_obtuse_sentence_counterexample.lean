import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_obtuse_sentence_counterexample
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5.Lean.Geometry.PathCore.obtuse_sentence_counterexample :
    ∀ {c : Fin 4 → Pt} (hc : IsPathConfig c (3 / 4) (1 / 4) (11 / 32)), isCommon c 0 2 ∧ betaA c 0 2 1 < π / 2 ∧ π / 2 < betaA c 0 2 3 ∧
      ell c 0 2 = 2 * betaA c 0 2 1 + 2 * betaA c 0 2 3 - 2 * π :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_obtuse_sentence_counterexample
