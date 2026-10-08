import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_divergence_path
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.divergence_path :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), 3*vol c Finset.univ = ∑ i, (pArea c i Finset.univ + inner ℝ (c i) (pMoment c i Finset.univ)) ∧
  ∑ i, pMoment c i Finset.univ = 0 :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_divergence_path
