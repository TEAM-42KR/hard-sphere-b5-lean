import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_labeled_patch_continuous_distinct
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.labeled_patch_continuous_distinct :
    ∀ (c : Fin 4 → Pt) (hinj : Function.Injective c) (i : Fin 4), ContinuousAt (fun c : Fin 4 → Pt => pArea c i Finset.univ) c ∧
  ContinuousAt (fun c : Fin 4 → Pt => pMoment c i Finset.univ) c :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_labeled_patch_continuous_distinct
