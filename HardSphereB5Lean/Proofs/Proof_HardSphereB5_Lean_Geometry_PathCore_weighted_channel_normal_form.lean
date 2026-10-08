import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_normal_form_volume
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_normal_form_patch
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_apex_anchor
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped RealInnerProductSpace Classical

private lemma p7w_q_inner (c : Fin 4 → Pt) (i j : Fin 4) :
    q c i j = inner ℝ (c j - c i) (c j - c i) := by
  rw [real_inner_self_eq_norm_sq]
  simp only [q, dist_eq_norm, norm_sub_rev]

private lemma p7w_inner_from_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (c j - c i) (c k - c i) = (q c i j + q c i k - q c j k) / 2 := by
  have h := norm_sub_sq_real (c j - c i) (c k - c i)
  have hv : (c j - c i) - (c k - c i) = c j - c k := by abel
  rw [hv] at h
  simp only [q, dist_eq_norm] at ⊢
  rw [norm_sub_rev (c i) (c j), norm_sub_rev (c i) (c k)]
  linarith

private lemma p7w_inner_coords (x y : Pt) :
    inner ℝ x y = x 0*y 0+x 1*y 1+x 2*y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]

private lemma p7w_cross_coords (v w : Pt) :
    cross v w = WithLp.toLp 2 ![v 1*w 2-v 2*w 1,
      v 2*w 0-v 0*w 2,v 0*w 1-v 1*w 0] := by
  simp [cross, SphereGeom.cross, cross_apply]

private lemma p7w_inner_endpoint_cross (d v w : Pt) :
    inner ℝ d (cross (v-w) (cross v w)) =
      (inner ℝ v w - inner ℝ w w) * inner ℝ d v -
        (inner ℝ v v - inner ℝ v w) * inner ℝ d w := by
  simp only [p7w_inner_coords, p7w_cross_coords]
  simp
  ring

private theorem p7w_scalarEndpointK_exact (c : Fin 4 → Pt) (l : Fin 4) :
    inner ℝ (c 1-c 3) (endTerm c 3 l) / Deltaf c 3 (oth1 3 l) (oth2 3 l) =
      scalarEndpointK c l := by
  unfold endTerm scalarEndpointK
  rw [p7w_inner_endpoint_cross, p7w_inner_from_q, ← p7w_q_inner, ← p7w_q_inner]
  rw [show
    (((q c 3 (oth1 3 l) + q c 3 (oth2 3 l) - q c (oth1 3 l) (oth2 3 l)) / 2 -
        q c 3 (oth2 3 l)) * inner ℝ (c 1-c 3) (c (oth1 3 l)-c 3) -
      (q c 3 (oth1 3 l) -
        (q c 3 (oth1 3 l) + q c 3 (oth2 3 l) - q c (oth1 3 l) (oth2 3 l)) / 2) *
        inner ℝ (c 1-c 3) (c (oth2 3 l)-c 3)) =
      ((q c 3 (oth1 3 l)-q c 3 (oth2 3 l)-q c (oth1 3 l) (oth2 3 l)) *
        inner ℝ (c 1-c 3) (c (oth1 3 l)-c 3) -
      (q c 3 (oth1 3 l)-q c 3 (oth2 3 l)+q c (oth1 3 l) (oth2 3 l)) *
        inner ℝ (c 1-c 3) (c (oth2 3 l)-c 3)) / 2 by ring,
    div_div]

private lemma p7w_scalarEndpointK_smul (c : Fin 4 → Pt) (l : Fin 4) (a : ℝ) :
    inner ℝ (c 1-c 3)
      ((a / (2 * Deltaf c 3 (oth1 3 l) (oth2 3 l))) • endTerm c 3 l) =
        a / 2 * scalarEndpointK c l := by
  rw [real_inner_smul_right, ← p7w_scalarEndpointK_exact]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private lemma p7w_ell_symm (c : Fin 4 → Pt) (i j : Fin 4) : ell c i j = ell c j i := by
  unfold ell
  rw [q, q, dist_comm]
  congr 3
  rw [Set.inter_comm (Metric.sphere (c i) 1) (Metric.sphere (c j) 1)]

private theorem p7w_channelArcCoeff_sum (c : Fin 4 → Pt) (X h ε : ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      (if i<j then channelArcCoeff c X h ε i j * ell c i j else 0)) =
    hcWeight X *
      (h / 2 * (∑ i : Fin 4, ∑ j : Fin 4,
          (if i<j then g (dist (c i) (c j)) * ell c i j else 0)) +
        h / 3 * (∑ j : Fin 4, (if j≠3 then dist (c 3) (c j)*ell c 3 j else 0)) -
        ε / 6 * (∑ j : Fin 4, (if j≠3 then
          (1-q c 3 j/4) / dist (c 3) (c j) * ell c 3 j *
            inner ℝ (c 1-c 3) (c j-c 3) else 0))) := by
  simp [Fin.sum_univ_succ, channelArcCoeff, q, p7w_ell_symm c 3 0,
    p7w_ell_symm c 3 1, p7w_ell_symm c 3 2, dist_comm (c 3) (c 0),
    dist_comm (c 3) (c 1), dist_comm (c 3) (c 2)]
  ring

private lemma p7w_channelCorner_sum (c : Fin 4 → Pt) (X h : ℝ) :
    channelCorner c X h = -hcWeight X*h/3 *
      ((∑ l, (nRet c l : ℝ)*sigmaF c l) +
        2 * (∑ l, if l≠3 then (nRet c l : ℝ)*gammaA c 3 (oth1 3 l) (oth2 3 l) else 0)) := by
  simp [channelCorner, Fin.sum_univ_succ]
  ring <;> simp

private theorem p7w_weighted_scalar_algebra_of_deps
    (W h ε p V A M Sg Eg Eq Cg Aa Am Ek H L : ℝ) (b : Prop)
    (hV : V = 8*p/3-Sg/3-Eg/2+Eq/12-(if b then H/12 else 0))
    (hA : A = 2*p-Cg-Aa/2)
    (hM : M = Am/2+Ek/2+(if b then H*L/8 else 0)) :
    W*(h*V+(2/3)*h*A+ε*M/3) =
      4*p*W*h-W*(h/2*Eg+h/3*Aa-ε/6*Am)-W*h/3*(Sg+2*Cg)+
      W*h/12*Eq+ε*W/6*Ek-(if b then W*h*H/12 else 0)+
      (if b then ε*W*H*L/24 else 0) := by
  rw [hV,hA,hM]
  by_cases hb : b <;> simp [hb] <;> ring

private theorem p7w_weighted_apex_sum {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) :
    inner ℝ (c 1-c 3) (∑ l : Fin 4, if l≠3 then apexTerm c 3 l else 0) =
      √(Hpoly X Y s)*Lapex c 3 0 2/8 := by
  simp only [inner_sum, apply_ite, inner_zero_right]
  norm_num [Fin.sum_univ_succ]
  rw [bulk_apex_anchor hc 3 0 1 (by decide), bulk_apex_anchor hc 3 1 1 (by decide),
    bulk_apex_anchor hc 3 2 1 (by decide)]
  simp [oth1,oth2]

private theorem p7w_normal_form_patch_scalar {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0) :
    inner ℝ (c 1-c 3) (pMoment c 3 Finset.univ) =
      (1/2) * (∑ j : Fin 4, if j≠3 then
        (1-q c 3 j/4) / dist (c 3) (c j) * ell c 3 j *
          inner ℝ (c 1-c 3) (c j-c 3) else 0) +
      (1/2) * (∑ l : Fin 4, if l≠3 then
        (nRet c l : ℝ)*√(Qface c l)*scalarEndpointK c l else 0) +
      (if 0<P4poly X Y s then √(Hpoly X Y s)*Lapex c 3 0 2/8 else 0) := by
  have hN := (HardSphereB5.Lean.Geometry.PathCore.normal_form_patch hc hP 3).2
  have hArc :
      inner ℝ (c 1-c 3) (∑ j : Fin 4, if j≠3 then
          ((1-q c 3 j/4) / dist (c 3) (c j) * ell c 3 j) • (c j-c 3) else 0) =
      ∑ j : Fin 4, if j≠3 then
        (1-q c 3 j/4) / dist (c 3) (c j) * ell c 3 j *
          inner ℝ (c 1-c 3) (c j-c 3) else 0 := by
    simp only [inner_sum, apply_ite, real_inner_smul_right, inner_zero_right]
  have hEnd :
      inner ℝ (c 1-c 3) (∑ l : Fin 4, if l≠3 then
        (((nRet c l : ℝ)*√(Qface c l) /
          (2 * Deltaf c 3 (oth1 3 l) (oth2 3 l))) • endTerm c 3 l) else 0) =
      (1/2) * (∑ l : Fin 4, if l≠3 then
        (nRet c l : ℝ)*√(Qface c l)*scalarEndpointK c l else 0) := by
    simp only [inner_sum, apply_ite, inner_zero_right, p7w_scalarEndpointK_smul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> ring
  rw [hN, inner_add_right, inner_add_right, real_inner_smul_right, hArc, hEnd]
  by_cases hb : 0<P4poly X Y s
  · simp only [hb, if_true]
    rw [p7w_weighted_apex_sum hc]
  · simp [hb]

private theorem p7w_weighted_channel_normal_form_of_deps {c : Fin 4 → Pt} {X Y s : ℝ}
    (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0) (h ε : ℝ)
    (hchannel : (h=channelH2 Y ∧ ε= -1) ∨ (h=channelH3 X Y s ∧ ε=1)) :
    channelDensity c X h ε = 4*π*hcWeight X*h -
      (∑ i, ∑ j, (if i<j then channelArcCoeff c X h ε i j * ell c i j else 0)) +
      channelCorner c X h + channelEndpoint c X Y s h ε := by
  have hV := HardSphereB5.Lean.Geometry.PathCore.normal_form_volume hc hP
  have hA := (HardSphereB5.Lean.Geometry.PathCore.normal_form_patch hc hP 3).1
  have hM := p7w_normal_form_patch_scalar hc hP
  rw [channelDensity,hV,hA,hM,p7w_channelArcCoeff_sum,p7w_channelCorner_sum,channelEndpoint]
  by_cases hb : 0<P4poly X Y s <;> simp only [hb,if_true,if_false] <;> ring

theorem proof_HardSphereB5_Lean_Geometry_PathCore_weighted_channel_normal_form {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0) (h ε : ℝ)
  (hchannel : (h=channelH2 Y ∧ ε= -1) ∨ (h=channelH3 X Y s ∧ ε=1)) :
  channelDensity c X h ε = 4*π*hcWeight X*h -
    (∑ i, ∑ j, (if i<j then channelArcCoeff c X h ε i j * ell c i j else 0)) +
    channelCorner c X h + channelEndpoint c X Y s h ε :=
  p7w_weighted_channel_normal_form_of_deps hc hP h ε hchannel

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_weighted_channel_normal_form
