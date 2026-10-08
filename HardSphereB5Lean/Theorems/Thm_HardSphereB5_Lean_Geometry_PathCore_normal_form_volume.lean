import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_normal_form_volume
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.normal_form_volume :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0), vol c Finset.univ = 8 * π / 3 - (1 / 3) * ∑ l, (nRet c l : ℝ) * sigmaF c l
      - (1 / 2) * ∑ i, ∑ j, (if i < j then g (dist (c i) (c j)) * ell c i j else 0)
      + (1 / 12) * ∑ l, (nRet c l : ℝ) * √(Qface c l)
      - (if 0 < P4poly X Y s then √(Hpoly X Y s) / 12 else 0) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_normal_form_volume
