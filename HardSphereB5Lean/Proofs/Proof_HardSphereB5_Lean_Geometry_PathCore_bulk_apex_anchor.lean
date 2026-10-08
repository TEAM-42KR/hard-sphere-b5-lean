import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_tetrahedron_metric
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

private lemma anchor_inner_coords (v w : Pt) :
    inner ℝ v w = v 0*w 0 + v 1*w 1 + v 2*w 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]

private lemma anchor_cross_coords (v w : Pt) :
    cross v w = WithLp.toLp 2 ![v 1*w 2-v 2*w 1, v 2*w 0-v 0*w 2, v 0*w 1-v 1*w 0] := by
  ext i
  fin_cases i <;> simp [HardSphereB5.Lean.Geometry.PathCore.cross, SphereGeom.cross, cross_apply]

private lemma anchor_orth_v (v w : Pt) : inner ℝ v (cross v w) = 0 := by
  rw [anchor_inner_coords, anchor_cross_coords]
  simp
  ring
private lemma anchor_orth_w (v w : Pt) : inner ℝ w (cross v w) = 0 := by
  rw [anchor_inner_coords, anchor_cross_coords]
  simp
  ring

private lemma anchor_det_coords (u v w : Pt) :
    det3 u v w = (u 1*v 2-u 2*v 1)*w 0 +
      (u 2*v 0-u 0*v 2)*w 1 + (u 0*v 1-u 1*v 0)*w 2 := by
  simp [det3,anchor_inner_coords,anchor_cross_coords]

private lemma anchor_real_sign_self (x : ℝ) : Real.sign x*x = |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h,abs_of_neg h];ring
  · rw [h];simp
  · rw [Real.sign_of_pos h,abs_of_pos h];ring

private lemma anchor_det_sq (c : Fin 4 → Pt) (i l : Fin 4) (hil : i ≠ l) :
    (det3 (c (oth1 i l)-c i) (c (oth2 i l)-c i) (c l-c i))^2 =
      (det3 (c 1-c 0) (c 2-c 0) (c 3-c 0))^2 := by
  fin_cases i <;> fin_cases l <;> simp_all only [Fin.isValue, ne_eq, not_true_eq_false]
  all_goals simp [oth1,oth2,anchor_det_coords]
  all_goals ring

private lemma anchor_label_exhaust (i l r : Fin 4) (hil : i ≠ l) :
    r = i ∨ r = l ∨ r = oth1 i l ∨ r = oth2 i l := by
  fin_cases i <;> fin_cases l <;> fin_cases r <;> simp_all [oth1,oth2] <;> decide

private lemma anchor_inner_det (c : Fin 4 → Pt) (i l : Fin 4) :
    inner ℝ (c l-c i) (cross (c (oth1 i l)-c i) (c (oth2 i l)-c i)) =
      det3 (c (oth1 i l)-c i) (c (oth2 i l)-c i) (c l-c i) := by
  exact real_inner_comm _ _

variable {c : Fin 4 → Pt} {X Y s : ℝ}
theorem proof_HardSphereB5_Lean_Geometry_PathCore_bulk_apex_anchor (hc : IsPathConfig c X Y s) (i l r : Fin 4) (hil : i≠l) :
  inner ℝ (c r-c i) (apexTerm c i l) =
    if r=l then √(Hpoly X Y s)*Lapex c i (oth1 i l) (oth2 i l)/8 else 0 := by
  have hg := (tetrahedron_metric hc).2.2.2.2
  have hd := anchor_det_sq c i l hil
  have ha : |det3 (c (oth1 i l)-c i) (c (oth2 i l)-c i) (c l-c i)| = √(Hpoly X Y s)/2 := by
    have hs := Real.sq_sqrt hc.H_pos.le
    have hab := abs_nonneg (det3 (c (oth1 i l)-c i) (c (oth2 i l)-c i) (c l-c i))
    have ha2 := sq_abs (det3 (c (oth1 i l)-c i) (c (oth2 i l)-c i) (c l-c i))
    nlinarith only [hg, hd, hs, hab, ha2, Real.sqrt_nonneg (Hpoly X Y s)]
  rcases anchor_label_exhaust i l r hil with rfl | rfl | rfl | rfl
  · simp [hil, apexTerm]
  · simp only [apexTerm, real_inner_smul_right, if_pos rfl, anchor_inner_det]
    have hs := anchor_real_sign_self (det3 (c (oth1 i r)-c i) (c (oth2 i r)-c i) (c r-c i))
    calc
      _ = Lapex c i (oth1 i r) (oth2 i r)/4 *
        (Real.sign (det3 (c (oth1 i r)-c i) (c (oth2 i r)-c i) (c r-c i)) *
        det3 (c (oth1 i r)-c i) (c (oth2 i r)-c i) (c r-c i)) := by
          clear hc hg hil hd ha hs
          ring
      _ = _ := by
          rw [hs,ha]
          simp only [if_true]
          clear hc hg hil hd ha hs
          ring
  · have hn : oth1 i l ≠ l := by fin_cases i <;> fin_cases l <;> decide
    simp [apexTerm,real_inner_smul_right,anchor_orth_v,hn]
  · have hn : oth2 i l ≠ l := by fin_cases i <;> fin_cases l <;> decide
    simp [apexTerm,real_inner_smul_right,anchor_orth_w,hn]
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_bulk_apex_anchor
