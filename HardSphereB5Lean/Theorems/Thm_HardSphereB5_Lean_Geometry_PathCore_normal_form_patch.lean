import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_normal_form_patch
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.normal_form_patch :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (i : Fin 4), pArea c i Finset.univ =
        2 * π - ∑ l, (if l ≠ i then (nRet c l : ℝ) * gammaA c i (oth1 i l) (oth2 i l) else 0)
          - (1 / 2) * ∑ j, (if j ≠ i then dist (c i) (c j) * ell c i j else 0) ∧
      pMoment c i Finset.univ =
        (1 / 2 : ℝ) • ∑ j, (if j ≠ i then
            ((1 - q c i j / 4) / dist (c i) (c j) * ell c i j) • (c j - c i) else 0)
          + ∑ l, (if l ≠ i then
              ((nRet c l : ℝ) * √(Qface c l) / (2 * Deltaf c i (oth1 i l) (oth2 i l))) •
                endTerm c i l else 0)
          + (if 0 < P4poly X Y s then ∑ l, (if l ≠ i then apexTerm c i l else 0) else 0) :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_normal_form_patch
