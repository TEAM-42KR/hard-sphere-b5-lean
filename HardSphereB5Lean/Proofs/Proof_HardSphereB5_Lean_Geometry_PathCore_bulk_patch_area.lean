import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_triple_patch_area
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_pair_width
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_incidence
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_Bridge_actual_patch_area_identity
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Real
section AreaScope1
open HardSphereB5.Lean (Pt)
variable {c:Fin 4→Pt} {X Y s:ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.BA_face_reindex (i : Fin 4) (A : Fin 4 → Fin 4 → ℝ) (E : Fin 4 → ℝ) :
    (∑ l : Fin 4,if l≠i then A (oth1 i l) (oth2 i l)+A (oth2 i l) (oth1 i l)+E l else 0)=
      (∑ j : Fin 4,if j≠i then A j (oth1 i j)+A j (oth2 i j) else 0)+
      (∑ l : Fin 4,if l≠i then E l else 0) := by
  fin_cases i <;> simp [Fin.sum_univ_succ,oth1,oth2] <;> abel

open HardSphereB5.Lean.Geometry.PathCore
private lemma HardSphereB5.Lean.Geometry.PathCore.BA_face_set (i l:Fin 4) (hil:i≠l) :
    faceSet l={i,oth1 i l,oth2 i l}:=by
  fin_cases i <;> fin_cases l <;> simp_all [faceSet,oth1,oth2] <;>decide

private lemma HardSphereB5.Lean.Geometry.PathCore.BA_triple_area (hc:IsPathConfig c X Y s) (i l:Fin 4) (hil:i≠l) :
    pArea c i (faceSet l)=2*π-2*gammaA c i (oth1 i l) (oth2 i l)-
      dist (c i) (c (oth1 i l))*betaA c i (oth1 i l) (oth2 i l)-
      dist (c i) (c (oth2 i l))*betaA c i (oth2 i l) (oth1 i l):=by
  have h1:i≠oth1 i l:=by fin_cases i <;>fin_cases l<;>simp_all[oth1]
  have h2:i≠oth2 i l:=by fin_cases i <;>fin_cases l<;>simp_all[oth2]
  have h3:oth1 i l≠oth2 i l:=by fin_cases i <;>fin_cases l<;>simp_all[oth1,oth2]
  rw [BA_face_set i l hil]
  simpa only [q,Real.sqrt_sq (dist_nonneg)] using triple_patch_area hc i (oth1 i l) (oth2 i l) h1 h2 h3

private theorem HardSphereB5.Lean.Geometry.PathCore.bulk_patch_area_of_raw (hc:IsPathConfig c X Y s) (hP:0<P4poly X Y s) (i:Fin 4)
    (hRaw:pArea c i Finset.univ=2*π-
      (∑ l:Fin 4,if l≠i then gammaA c i (oth1 i l) (oth2 i l) else 0)-
      (1/2)*(∑ j:Fin 4,if j≠i then dist (c i) (c j)*ell c i j else 0)) :
    pArea c i Finset.univ=-π+(1/2)*(∑ l,if l≠i then pArea c i (faceSet l) else 0)+
      (1/2)*(∑ j,if j≠i then dist (c i) (c j)*phiE c i j else 0):=by
  have hBeta (j:Fin 4) (hji:j≠i):ell c i j=betaA c i j (oth1 i j)+betaA c i j (oth2 i j)-phiE c i j:=by
    have h:=pair_width hc hP.ne' i j (Ne.symm hji)
    have hc1: nRet c (oth1 i j)=1:=(bulk_incidence hc hP).1 _
    have hc2: nRet c (oth2 i j)=1:=(bulk_incidence hc hP).1 _
    have hs:¬(P4poly X Y s<0∧isCommon c i j):=by intro hs;exact (not_lt_of_gt hP) hs.1
    simpa only [hc1,hc2,Nat.cast_one,one_mul,if_pos hP,if_neg hs,sub_zero,add_comm] using h
  have he : (∑ j:Fin 4,if j≠i then dist (c i) (c j)*ell c i j else 0)=
      (∑ j:Fin 4,if j≠i then dist (c i) (c j)*betaA c i j (oth1 i j)+
        dist (c i) (c j)*betaA c i j (oth2 i j) else 0)-
      (∑ j:Fin 4,if j≠i then dist (c i) (c j)*phiE c i j else 0):=by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji:j=i
    · simp[hji]
    · simp only [if_pos hji,hBeta j hji,mul_sub,mul_add]
  have ht : (∑ l:Fin 4,if l≠i then pArea c i (faceSet l) else 0)=
      6*π-2*(∑ l:Fin 4,if l≠i then gammaA c i (oth1 i l) (oth2 i l) else 0)-
      (∑ j:Fin 4,if j≠i then dist (c i) (c j)*betaA c i j (oth1 i j)+
        dist (c i) (c j)*betaA c i j (oth2 i j) else 0):=by
    have hs (l:Fin 4):(if l≠i then pArea c i (faceSet l) else 0)=
        (if l≠i then 2*π-2*gammaA c i (oth1 i l) (oth2 i l) else 0)-
        (if l≠i then dist (c i) (c (oth1 i l))*betaA c i (oth1 i l) (oth2 i l)+
          dist (c i) (c (oth2 i l))*betaA c i (oth2 i l) (oth1 i l) else 0):=by
      by_cases hil:l=i
      · simp[hil]
      · rw [if_pos hil,if_pos hil,if_pos hil,BA_triple_area hc i l (Ne.symm hil)];ring
    simp_rw [hs]
    rw [Finset.sum_sub_distrib]
    have hr:=BA_face_reindex i (fun j k=>dist (c i) (c j)*betaA c i j k) (fun _=>0)
    simp only [add_zero,ite_self,Finset.sum_const_zero] at hr
    rw [hr]
    congr 1
    fin_cases i <;>simp[Fin.sum_univ_succ]<;>ring
  rw [hRaw,he,ht]
  ring
end AreaScope1

theorem proof_HardSphereB5_Lean_Geometry_PathCore_bulk_patch_area {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s) (i : Fin 4) :
    pArea c i Finset.univ = -π+(1/2)*(∑ l,if l≠i then pArea c i (faceSet l) else 0)+
      (1/2)*(∑ j,if j≠i then dist (c i) (c j)*phiE c i j else 0) := by
  exact bulk_patch_area_of_raw hc hP i
    (HardSphereB5.Lean.Geometry.PathCore.Bridge.actual_patch_area_identity hc hP i)
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_bulk_patch_area
