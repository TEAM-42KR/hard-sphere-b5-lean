import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import Mathlib
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_table
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_pair_width
set_option autoImplicit false

noncomputable section
open MeasureTheory Real
private abbrev HardSphereB5.Lean.Geometry.PathCore.s5c_scope_anchor_obtuse_sentence_counterexample : Unit := ()
section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private theorem HardSphereB5.Lean.Geometry.PathCore.obtuse_point_beta_signs (hc : IsPathConfig c (3 / 4) (1 / 4) (11 / 32)) :
    betaA c 0 2 1 < π / 2 ∧ π / 2 < betaA c 0 2 3 := by
  have hsym (i j : Fin 4) : q c i j = q c j i := by simp [q, dist_comm]
  have hreal1 : √(q c 0 2) * (q c 0 1 + q c 2 1 - q c 0 2) = 3 / 4 := by
    rw [hc.q02, hc.q01, hsym 2 1, hc.q12]
    norm_num
  have hreal3 : √(q c 0 2) * (q c 0 3 + q c 2 3 - q c 0 2) = -13 / 32 := by
    rw [hc.q02, hc.q03, hc.q23]
    norm_num
  constructor
  · unfold betaA atan2
    apply Complex.arg_lt_pi_div_two_iff.mpr
    left
    change 0 < √(q c 0 2) * (q c 0 1 + q c 2 1 - q c 0 2)
    rw [hreal1]
    norm_num
  · apply lt_of_not_ge
    intro hle
    have hh := Complex.arg_le_pi_div_two_iff.mp hle
    rcases hh with hx | hy
    · change 0 ≤ √(q c 0 2) * (q c 0 3 + q c 2 3 - q c 0 2) at hx
      rw [hreal3] at hx
      norm_num at hx
    · change 2 * √(Qf c 0 2 3) < 0 at hy
      exact (by positivity : 0 ≤ 2 * √(Qf c 0 2 3)).not_gt hy

private theorem HardSphereB5.Lean.Geometry.PathCore.obtuse_sentence_counterexample_of_deps
(hTable : ∀ {c : Fin 4 → Pt} {X Y s : ℝ}, ∀ (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0),
(s < 1 → Y < X → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (2, 0, 2, 0) ∧ isCommon c 0 2) ∧
    (s < 1 → X < Y → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (0, 2, 0, 2) ∧ isCommon c 1 3) ∧
    (1 < s → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (0, 0, 2, 2) ∧ isCommon c 2 3))
(hWidth : ∀ {c : Fin 4 → Pt} {X Y s : ℝ}, ∀ (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (i j : Fin 4) (hij : i ≠ j),
ell c i j = (nRet c (oth2 i j) : ℝ) * betaA c i j (oth1 i j)
        + (nRet c (oth1 i j) : ℝ) * betaA c i j (oth2 i j)
        - (if 0 < P4poly X Y s then phiE c i j else 0)
        - (if P4poly X Y s < 0 ∧ isCommon c i j then 2 * π else 0))
(hc : IsPathConfig c (3 / 4) (1 / 4) (11 / 32)) :
    isCommon c 0 2 ∧ betaA c 0 2 1 < π / 2 ∧ π / 2 < betaA c 0 2 3 ∧
      ell c 0 2 = 2 * betaA c 0 2 1 + 2 * betaA c 0 2 3 - 2 * π := by
  have hP : P4poly (3 / 4) (1 / 4) (11 / 32) < 0 := by norm_num [P4poly]
  have hcommon : isCommon c 0 2 :=
    ((hTable hc hP).1 (by norm_num) (by norm_num)).2
  have hwidth := hWidth hc hP.ne 0 2 (by decide)
  have hn1 : nRet c 1 = 2 := by
    have hh := ((hTable hc hP).1 (by norm_num) (by norm_num)).1
    exact congrArg (fun t : ℕ × ℕ × ℕ × ℕ => t.2.2.1) hh
  have hn3 : nRet c 3 = 2 := by
    have hh := ((hTable hc hP).1 (by norm_num) (by norm_num)).1
    exact congrArg (fun t : ℕ × ℕ × ℕ × ℕ => t.1) hh
  have hnotpos : ¬0 < P4poly (3 / 4) (1 / 4) (11 / 32) := not_lt.mpr hP.le
  have ho1 : oth1 (0 : Fin 4) 2 = 1 := by decide
  have ho2 : oth2 (0 : Fin 4) 2 = 3 := by decide
  rw [ho1, ho2, hn1, hn3] at hwidth
  have hcond : P4poly (3 / 4) (1 / 4) (11 / 32) < 0 ∧ isCommon c 0 2 := ⟨hP, hcommon⟩
  simp only [Nat.cast_ofNat, if_neg hnotpos, if_pos hcond, sub_zero] at hwidth
  obtain ⟨hsign1, hsign3⟩ := obtuse_point_beta_signs hc
  exact ⟨hcommon, hsign1, hsign3, hwidth⟩

end

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical RealInnerProductSpace
variable {c : Fin 4 → Pt} {X Y s : ℝ}
theorem proof_HardSphereB5_Lean_Geometry_PathCore_obtuse_sentence_counterexample (hc : IsPathConfig c (3 / 4) (1 / 4) (11 / 32)) :
    isCommon c 0 2 ∧ betaA c 0 2 1 < π / 2 ∧ π / 2 < betaA c 0 2 3 ∧
      ell c 0 2 = 2 * betaA c 0 2 1 + 2 * betaA c 0 2 3 - 2 * π := by
  exact obtuse_sentence_counterexample_of_deps sliver_table pair_width hc
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_obtuse_sentence_counterexample
