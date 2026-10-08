import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_realizable_classification
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.realizable_classification :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ}
    (hc : IsPathConfig c X Y s), ∃ φ : Pt ≃ᵃⁱ[ℝ] Pt, ∀ i, φ (c i) = canonicalCenters X Y s i :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_realizable_classification
