import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_patch_area
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_patch_moment
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_patch_valuation
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_triple_patch_area
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_triple_patch_moment
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_incidence
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_pair_width
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_pathFaceQ_pos
import HardSphereB5Lean.Theorems.Thm_SolidGeom_area_moment_pair_cap
set_option autoImplicit false

set_option maxHeartbeats 2000000

noncomputable section
open MeasureTheory Real HardSphereB5.Lean
private abbrev HardSphereB5.Lean.Geometry.PathCore.s5c_scope_anchor_normal_form_patch : Unit := ()
section
open HardSphereB5.Lean.Geometry.PathCore

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_q_sym (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by simp [q, dist_comm]
private lemma HardSphereB5.Lean.Geometry.PathCore.p8_sqrt_q (c : Fin 4 → Pt) (i j : Fin 4) : √(q c i j) = dist (c i) (c j) := by
  exact Real.sqrt_sq (dist_nonneg)

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_face_set (i l : Fin 4) (hil : i ≠ l) :
    faceSet l = {i, oth1 i l, oth2 i l} := by
  fin_cases i <;> fin_cases l <;> simp_all [faceSet, oth1, oth2, Fin.univ_succ] <;> decide

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_face_q (c : Fin 4 → Pt) (i l : Fin 4) (hil : i ≠ l) :
    Qface c l = Qf c i (oth1 i l) (oth2 i l) := by
  have h10 := dist_comm (c 1) (c 0)
  have h20 := dist_comm (c 2) (c 0)
  have h30 := dist_comm (c 3) (c 0)
  have h21 := dist_comm (c 2) (c 1)
  have h31 := dist_comm (c 3) (c 1)
  have h32 := dist_comm (c 3) (c 2)
  fin_cases i <;> fin_cases l <;>
    simp_all [Qface, faceVerts, oth1, oth2, Qf, QT, DeltaT, q, h10, h20, h30, h21, h31, h32] <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_face_distinct (i l : Fin 4) (hil : i ≠ l) :
    i ≠ oth1 i l ∧ i ≠ oth2 i l ∧ oth1 i l ≠ oth2 i l := by
  fin_cases i <;> fin_cases l <;> simp_all [oth1, oth2]

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_triple_area {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (i l : Fin 4) (hil : i ≠ l) :
    pArea c i (faceSet l) = 2 * π - 2 * gammaA c i (oth1 i l) (oth2 i l) -
      dist (c i) (c (oth1 i l)) * betaA c i (oth1 i l) (oth2 i l) -
      dist (c i) (c (oth2 i l)) * betaA c i (oth2 i l) (oth1 i l) := by
  rcases p8_face_distinct i l hil with ⟨h1,h2,h12⟩
  rw [p8_face_set i l hil, triple_patch_area hc i _ _ h1 h2 h12,
    p8_sqrt_q, p8_sqrt_q]

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_triple_moment {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (i l : Fin 4) (hil : i ≠ l) :
    pMoment c i (faceSet l) =
      ((1-q c i (oth1 i l)/4)/dist (c i) (c (oth1 i l)) * betaA c i (oth1 i l) (oth2 i l)) • (c (oth1 i l)-c i) +
      ((1-q c i (oth2 i l)/4)/dist (c i) (c (oth2 i l)) * betaA c i (oth2 i l) (oth1 i l)) • (c (oth2 i l)-c i) +
      (√(Qface c l)/Deltaf c i (oth1 i l) (oth2 i l)) • endTerm c i l := by
  rcases p8_face_distinct i l hil with ⟨h1,h2,h12⟩
  rw [p8_face_set i l hil, triple_patch_moment hc i _ _ h1 h2 h12,
    p8_sqrt_q, p8_sqrt_q, ← p8_face_q c i l hil]
  rfl

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_pair_bounds {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (i j : Fin 4) (hij : i ≠ j) : 0 < dist (c i) (c j) ∧ dist (c i) (c j) < 2 := by
  let k := oth1 i j
  have hik : i ≠ k := (p8_face_distinct i j hij).1
  have hjk : j ≠ k := by
    fin_cases i <;> fin_cases j <;> simp_all [k, oth1]
  have hQ : 0 < Qf c i j k := HardSphereB5.Lean.Geometry.pathFaceQ_pos c X Y s
    hc.q01 hc.q02 hc.q03 hc.q12 hc.q13 hc.q23 hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one hc.H_pos i j k hij hik hjk
  let a := q c i j
  let b := q c i k
  let d := q c j k
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hd : 0 ≤ d := sq_nonneg _
  have habd : 0 ≤ a*b*d := mul_nonneg (mul_nonneg ha hb) hd
  have hDelta : 0 < DeltaT a b d := by change 0 < DeltaT a b d - a*b*d at hQ; linarith
  have hpoly : DeltaT a b d * (4-a) = a*(b+d-a)^2+4*QT a b d := by simp only [QT, DeltaT]; ring
  have hpos : 0 < DeltaT a b d * (4-a) := by
    rw [hpoly]
    have hn : 0 ≤ a * (b+d-a)^2 := mul_nonneg ha (sq_nonneg _)
    change 0 < QT a b d at hQ
    linarith
  have ha4 : a < 4 := by nlinarith
  have ha0 : 0 < a := by
    change 0 < 4*a*b-(a+b-d)^2-a*b*d at hQ
    by_contra h
    have haeq : a = 0 := le_antisymm (le_of_not_gt h) ha
    rw [haeq] at hQ
    nlinarith [sq_nonneg (b-d)]
  have hdist : 0 ≤ dist (c i) (c j) := dist_nonneg
  change 0 < dist (c i) (c j)^2 at ha0
  change dist (c i) (c j)^2 < 4 at ha4
  constructor <;> nlinarith

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_sliver_counts {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (hP : P4poly X Y s < 0) (a b : Fin 4) (hab : a ≠ b) (hcom : isCommon c a b) :
    ∀ l, nRet c l = if l ≠ a ∧ l ≠ b then 2 else 0 := by
  have hnum := (sliver_incidence hc hP).1
  have hsum := (sliver_incidence hc hP).2.1
  have h02 : ∀ l, nRet c l = 0 ∨ nRet c l = 2 := by
    intro l; rw [hnum l]; split_ifs <;> simp
  have h0 := h02 0; have h1 := h02 1; have h2 := h02 2; have h3 := h02 3
  clear hnum h02
  simp [Fin.sum_univ_four] at hsum
  intro l
  fin_cases a <;> fin_cases b <;> fin_cases l <;>
    simp_all [isCommon, oth1, oth2] <;> omega

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_sliver_common {c : Fin 4 → Pt} (a b i j : Fin 4) (hab : a ≠ b) (hij : i ≠ j)
    (hcount : ∀ l, nRet c l = if l ≠ a ∧ l ≠ b then 2 else 0) :
    isCommon c i j ↔ (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp_all [isCommon, oth1, oth2, hcount]

end

section
open HardSphereB5.Lean.Geometry.PathCore

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_self_ball_ae (x : Pt) : ∀ᵐ u ∂sphereMeasure x, u ∈ Metric.closedBall x 1 := by
  unfold sphereMeasure SphereGeom.sphereMeasure
  rw [ae_map_iff (by fun_prop) (by measurability)]
  apply ae_of_all
  intro u
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hu : ‖(u : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using u.property
  simpa [hu]

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_pair_patches {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
    (i j : Fin 4) (hij : i ≠ j) :
    pArea c i {i,j} = 2*π-π*dist (c i) (c j) ∧
    pMoment c i {i,j} = (π*(1-q c i j/4)/dist (c i) (c j)) • (c j-c i) := by
  rcases p8_pair_bounds hc i j hij with ⟨h0,h2⟩
  have hcap := SolidGeom.area_moment_pair_cap (c i) (c j) h0 h2
  have hbody : body c {i,j} = Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1 := by
    ext x
    simp [body]
  have hsets : body c {i,j} =ᵐ[sphereMeasure (c i)] Metric.closedBall (c j) 1 := by
    filter_upwards [p8_self_ball_ae (c i)] with u hu
    rw [hbody]
    apply propext
    change (u ∈ Metric.closedBall (c i) 1 ∧ u ∈ Metric.closedBall (c j) 1) ↔ _
    exact ⟨And.right, fun h => ⟨hu,h⟩⟩
  have hA := measure_congr hsets
  have hM := setIntegral_congr_set (f := fun x : Pt => x-c i) hsets
  simp only [pArea, pMoment, Finset.mem_insert_self, if_pos] at ⊢
  rw [hA, hM]
  constructor
  · rw [hcap.1]; ring
  · exact hcap.2

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_sliver_face_valuation {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0)
    (a b : Fin 4) (hab : a ≠ b) (hcom : isCommon c a b)
    (hcount : ∀ l, nRet c l = if l ≠ a ∧ l ≠ b then 2 else 0) (i : Fin 4) :
    pArea c i Finset.univ =
      (1/2)*∑ l, (if l ≠ i then (nRet c l : ℝ)*pArea c i (faceSet l) else 0) - pArea c i {a,b} ∧
    pMoment c i Finset.univ =
      (1/2 : ℝ) • ∑ l, (if l ≠ i then (nRet c l : ℝ) • pMoment c i (faceSet l) else 0) - pMoment c i {a,b} := by
  have hset1 : ({a,b,oth1 a b} : Finset (Fin 4)) = faceSet (oth2 a b) := by
    fin_cases a <;> fin_cases b <;> simp_all [oth1,oth2,faceSet,Fin.univ_succ] <;> decide
  have hset2 : ({a,b,oth2 a b} : Finset (Fin 4)) = faceSet (oth1 a b) := by
    fin_cases a <;> fin_cases b <;> simp_all [oth1,oth2,faceSet,Fin.univ_succ] <;> decide
  have hv := sliver_patch_valuation hc hP a b hab hcom i
  rw [hset1,hset2] at hv
  have hselfA : pArea c i (faceSet i) = 0 := by simp [pArea,faceSet]
  have hselfM : pMoment c i (faceSet i) = 0 := by simp [pMoment,faceSet]
  have hsA : (1/2)*∑ l, (if l ≠ i then (nRet c l : ℝ)*pArea c i (faceSet l) else 0) =
      pArea c i (faceSet (oth2 a b))+pArea c i (faceSet (oth1 a b)) := by
    fin_cases a <;> fin_cases b <;> fin_cases i <;>
      simp_all [Fin.sum_univ_four, oth1,oth2,hcount] <;> ring
  have hsM : (1/2 : ℝ) • ∑ l, (if l ≠ i then (nRet c l : ℝ) • pMoment c i (faceSet l) else 0) =
      pMoment c i (faceSet (oth2 a b))+pMoment c i (faceSet (oth1 a b)) := by
    fin_cases a <;> fin_cases b <;> fin_cases i <;>
      simp_all [Fin.sum_univ_four,oth1,oth2,hcount] <;> module
  rw [hsA,hsM]
  exact hv

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_area_face_sum (c : Fin 4 → Pt) (i : Fin 4) (n : Fin 4 → ℝ)
    (hA : ∀ l, l ≠ i → pArea c i (faceSet l) =
      2*π-2*gammaA c i (oth1 i l) (oth2 i l) -
      dist (c i) (c (oth1 i l))*betaA c i (oth1 i l) (oth2 i l) -
      dist (c i) (c (oth2 i l))*betaA c i (oth2 i l) (oth1 i l)) :
    (1/2)*∑ l, (if l ≠ i then n l*pArea c i (faceSet l) else 0) =
      π*∑ l, (if l ≠ i then n l else 0) -
      ∑ l, (if l ≠ i then n l*gammaA c i (oth1 i l) (oth2 i l) else 0) -
      (1/2)*∑ j, (if j ≠ i then dist (c i) (c j)*
        (n (oth2 i j)*betaA c i j (oth1 i j)+n (oth1 i j)*betaA c i j (oth2 i j)) else 0) := by
  fin_cases i <;> simp_all [Fin.sum_univ_four, oth1, oth2] <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_moment_face_sum (c : Fin 4 → Pt) (i : Fin 4) (n : Fin 4 → ℝ)
    (hM : ∀ l, l ≠ i → pMoment c i (faceSet l) =
      ((1-q c i (oth1 i l)/4)/dist (c i) (c (oth1 i l))*betaA c i (oth1 i l) (oth2 i l)) • (c (oth1 i l)-c i) +
      ((1-q c i (oth2 i l)/4)/dist (c i) (c (oth2 i l))*betaA c i (oth2 i l) (oth1 i l)) • (c (oth2 i l)-c i) +
      (√(Qface c l)/Deltaf c i (oth1 i l) (oth2 i l)) • endTerm c i l) :
    (1/2 : ℝ) • ∑ l, (if l ≠ i then n l • pMoment c i (faceSet l) else 0) =
      (1/2 : ℝ) • ∑ j, (if j ≠ i then
        ((1-q c i j/4)/dist (c i) (c j)*
          (n (oth2 i j)*betaA c i j (oth1 i j)+n (oth1 i j)*betaA c i j (oth2 i j))) • (c j-c i) else 0) +
      ∑ l, (if l ≠ i then (n l*√(Qface c l)/(2*Deltaf c i (oth1 i l) (oth2 i l))) • endTerm c i l else 0) := by
  fin_cases i <;> simp_all [Fin.sum_univ_four, oth1, oth2, div_eq_mul_inv, mul_inv_rev] <;> module

end

section
open HardSphereB5.Lean.Geometry.PathCore
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_pair_at_patch (hc : IsPathConfig c X Y s) (a b i : Fin 4) (hab : a ≠ b) :
    pArea c i {a,b} =
      (if i = a then 2*π-π*dist (c i) (c b) else if i = b then 2*π-π*dist (c i) (c a) else 0) ∧
    pMoment c i {a,b} =
      (if i = a then (π*(1-q c i b/4)/dist (c i) (c b)) • (c b-c i)
        else if i = b then (π*(1-q c i a/4)/dist (c i) (c a)) • (c a-c i) else 0) := by
  by_cases hia : i = a
  · subst i
    simpa [hab] using p8_pair_patches hc a b hab
  · by_cases hib : i = b
    · subst i
      simpa [hia, Finset.pair_comm] using p8_pair_patches hc b a hab.symm
    · simp [pArea,pMoment,hia,hib]

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_excluded_sum {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) (i : Fin 4) :
    ∑ l : Fin 4, (if l ≠ i then f l else 0) = ∑ l ∈ Finset.univ.erase i, f l := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero,add_zero]
  have hs : Finset.univ.filter (fun l : Fin 4 => l ≠ i) = Finset.univ.erase i := by
    ext l; simp [ne_comm]
  rw [hs]

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_selector_sum {M : Type*} [AddCommMonoid M] (f : Fin 4 → M)
    (a b i : Fin 4) (hab : a ≠ b) :
    ∑ j : Fin 4, (if j ≠ i then (if (i=a ∧ j=b) ∨ (i=b ∧ j=a) then f j else 0) else 0) =
      if i=a then f b else if i=b then f a else 0 := by
  classical
  by_cases ha : i=a
  · subst i
    simp [hab,hab.symm,Finset.sum_ite_eq']
    calc
      _ = ∑ j : Fin 4, (if j=b then f j else 0) := by
        apply Finset.sum_congr rfl; intro j _
        by_cases hj : j=a
        · subst j; simp [hab]
        · simp [hj]
      _ = _ := by simp
  · by_cases hb : i=b
    · subst i
      simp [ha,hab,hab.symm,Finset.sum_ite_eq']
      calc
        _ = ∑ j : Fin 4, (if j=a then f j else 0) := by
          apply Finset.sum_congr rfl; intro j _
          by_cases hj : j=b
          · subst j; simp [hab.symm]
          · simp [hj]
        _ = _ := by simp
    · simp [ha,hb]

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_width_scalar_sum (c : Fin 4 → Pt) (i : Fin 4) (B S : Fin 4 → ℝ)
    (hw : ∀ j, j ≠ i → B j = ell c i j + S j) :
    ∑ j, (if j ≠ i then dist (c i) (c j)*B j else 0) =
      (∑ j, (if j ≠ i then dist (c i) (c j)*ell c i j else 0)) +
      (∑ j, (if j ≠ i then dist (c i) (c j)*S j else 0)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j=i
  · simp [hj]
  · rw [if_pos hj,if_pos hj,if_pos hj,hw j hj]
    ring

private lemma HardSphereB5.Lean.Geometry.PathCore.p8_width_vector_sum (c : Fin 4 → Pt) (i : Fin 4) (B S : Fin 4 → ℝ)
    (hw : ∀ j, j ≠ i → B j = ell c i j + S j) :
    ∑ j, (if j ≠ i then ((1-q c i j/4)/dist (c i) (c j)*B j) • (c j-c i) else 0) =
      (∑ j, (if j ≠ i then ((1-q c i j/4)/dist (c i) (c j)*ell c i j) • (c j-c i) else 0)) +
      (∑ j, (if j ≠ i then ((1-q c i j/4)/dist (c i) (c j)*S j) • (c j-c i) else 0)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j=i
  · simp [hj]
  · rw [if_pos hj,if_pos hj,if_pos hj,hw j hj]
    module

private theorem HardSphereB5.Lean.Geometry.PathCore.normal_form_patch_of_deps (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (i : Fin 4) :
    pArea c i Finset.univ =
        2 * π - ∑ l, (if l ≠ i then (nRet c l : ℝ) * gammaA c i (oth1 i l) (oth2 i l) else 0)
          - (1 / 2) * ∑ j, (if j ≠ i then dist (c i) (c j) * ell c i j else 0) ∧
      pMoment c i Finset.univ =
        (1 / 2 : ℝ) • ∑ j, (if j ≠ i then
            ((1 - q c i j / 4) / dist (c i) (c j) * ell c i j) • (c j - c i) else 0)
          + ∑ l, (if l ≠ i then
              ((nRet c l : ℝ) * √(Qface c l) / (2 * Deltaf c i (oth1 i l) (oth2 i l))) •
                endTerm c i l else 0)
          + (if 0 < P4poly X Y s then ∑ l, (if l ≠ i then apexTerm c i l else 0) else 0) := by
  have hTA := fun l (hl : l ≠ i) => p8_triple_area hc i l hl.symm
  have hTM := fun l (hl : l ≠ i) => p8_triple_moment hc i l hl.symm
  by_cases hPb : 0 < P4poly X Y s
  · have hn := (bulk_incidence hc hPb).1
    have hA := HardSphereB5.Lean.Geometry.PathCore.bulk_patch_area hc hPb i
    have hM := HardSphereB5.Lean.Geometry.PathCore.bulk_patch_moment hc hPb i
    let B := fun j => betaA c i j (oth1 i j)+betaA c i j (oth2 i j)
    have hw : ∀ j, j ≠ i → B j = ell c i j + phiE c i j := by
      intro j hj
      have hp := pair_width hc hP i j hj.symm
      have hPn : ¬ P4poly X Y s < 0 := not_lt_of_ge hPb.le
      have hnot : ¬ (P4poly X Y s < 0 ∧ isCommon c i j) := fun hh => hPn hh.1
      simp only [hn,Nat.cast_one,one_mul,if_pos hPb,if_neg hnot,sub_zero] at hp
      dsimp [B]; linarith
    have hAS := p8_area_face_sum c i (fun _ => (1 : ℝ)) hTA
    have hMS := p8_moment_face_sum c i (fun _ => (1 : ℝ)) hTM
    simp only [one_mul,one_smul] at hAS hMS
    have hthree : ∑ l : Fin 4, (if l ≠ i then (1 : ℝ) else 0) = 3 := by
      rw [p8_excluded_sum]; simp
    have hDS := p8_width_scalar_sum c i B (phiE c i) hw
    have hVS := p8_width_vector_sum c i B (phiE c i) hw
    constructor
    · rw [hA,hAS,hthree,hDS]
      simp only [hn,Nat.cast_one,one_mul]
      ring
    · rw [hM,hMS,hVS]
      simp only [hn,Nat.cast_one,one_mul,p8_sqrt_q,if_pos hPb]
      module
  · have hPs : P4poly X Y s < 0 := lt_of_le_of_ne (le_of_not_gt hPb) hP
    obtain ⟨a,b,hab,hcom,hdeg⟩ := (sliver_incidence hc hPs).2.2
    have hn := p8_sliver_counts hc hPs a b hab hcom
    have hv := p8_sliver_face_valuation hc hPs a b hab hcom hn i
    have hcap := p8_pair_at_patch hc a b i hab
    let B := fun j => (nRet c (oth2 i j) : ℝ)*betaA c i j (oth1 i j)+
      (nRet c (oth1 i j) : ℝ)*betaA c i j (oth2 i j)
    let S := fun j => if (i=a ∧ j=b) ∨ (i=b ∧ j=a) then 2*π else 0
    have hw : ∀ j, j ≠ i → B j = ell c i j + S j := by
      intro j hj
      have hp := pair_width hc hP i j hj.symm
      simp only [if_neg hPb,sub_zero] at hp
      have hh := p8_sliver_common a b i j hab hj.symm hn
      simp only [hPs,true_and,hh] at hp
      dsimp [B,S]; linarith
    have hAS := p8_area_face_sum c i (fun l => (nRet c l : ℝ)) hTA
    have hMS := p8_moment_face_sum c i (fun l => (nRet c l : ℝ)) hTM
    have hN : ∑ l : Fin 4, (if l ≠ i then (nRet c l : ℝ) else 0) =
        if i=a ∨ i=b then 4 else 2 := by
      rw [p8_excluded_sum,← Nat.cast_sum,hdeg]
      split_ifs <;> norm_num
    have hDS := p8_width_scalar_sum c i B S hw
    have hVS := p8_width_vector_sum c i B S hw
    have hD : ∑ j, (if j ≠ i then dist (c i) (c j)*S j else 0) =
        if i=a then 2*π*dist (c i) (c b) else if i=b then 2*π*dist (c i) (c a) else 0 := by
      calc
        _ = ∑ j : Fin 4, (if j ≠ i then
          (if (i=a ∧ j=b) ∨ (i=b ∧ j=a) then 2*π*dist (c i) (c j) else 0) else 0) := by
            apply Finset.sum_congr rfl; intro j _; dsimp [S]; split_ifs <;> ring
        _ = _ := p8_selector_sum _ a b i hab
    have hV : (1/2 : ℝ) • ∑ j, (if j ≠ i then
        ((1-q c i j/4)/dist (c i) (c j)*S j) • (c j-c i) else 0) = pMoment c i {a,b} := by
      rw [hcap.2,Finset.smul_sum]
      calc
        _ = ∑ j : Fin 4, (if j ≠ i then
          (if (i=a ∧ j=b) ∨ (i=b ∧ j=a) then (π*(1-q c i j/4)/dist (c i) (c j)) • (c j-c i) else 0) else 0) := by
            apply Finset.sum_congr rfl; intro j _; dsimp [S]; split_ifs <;> module
        _ = _ := p8_selector_sum _ a b i hab
    constructor
    · rw [hv.1,hAS,hDS,hN,hD,hcap.1]
      by_cases ha : i=a
      · subst i; simp [hab,hab.symm]; ring
      · by_cases hb : i=b
        · subst i; simp [ha,hab,hab.symm]; ring
        · simp [ha,hb]; ring
    · rw [hv.2,hMS,hVS]
      simp only [if_neg hPb,add_zero]
      rw [smul_add,hV]
      module

theorem proof_HardSphereB5_Lean_Geometry_PathCore_normal_form_patch {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (i : Fin 4) :
    pArea c i Finset.univ =
        2 * π - ∑ l, (if l ≠ i then (nRet c l : ℝ) * gammaA c i (oth1 i l) (oth2 i l) else 0)
          - (1 / 2) * ∑ j, (if j ≠ i then dist (c i) (c j) * ell c i j else 0) ∧
      pMoment c i Finset.univ =
        (1 / 2 : ℝ) • ∑ j, (if j ≠ i then
            ((1 - q c i j / 4) / dist (c i) (c j) * ell c i j) • (c j - c i) else 0)
          + ∑ l, (if l ≠ i then
              ((nRet c l : ℝ) * √(Qface c l) / (2 * Deltaf c i (oth1 i l) (oth2 i l))) •
                endTerm c i l else 0)
          + (if 0 < P4poly X Y s then ∑ l, (if l ≠ i then apexTerm c i l else 0) else 0) := by
  exact normal_form_patch_of_deps hc hP i

#print axioms normal_form_patch_of_deps
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_normal_form_patch
end
