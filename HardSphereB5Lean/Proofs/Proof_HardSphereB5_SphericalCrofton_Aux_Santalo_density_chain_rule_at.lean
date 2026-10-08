import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_sigma_gram_data
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_cap_density_algebra
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_primitive_chain
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_distance_identity
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_rho_rational
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

private theorem triples (n m p q : Pt) :
    inner ℝ (cross n p) q = inner ℝ n (cross p q) ∧
    inner ℝ p (-cross m q) = inner ℝ m (cross p q) := by
  have hi (z w : Pt) : inner ℝ z w = z 0*w 0+z 1*w 1+z 2*w 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]; ring
  simp_rw [hi]
  simp only [SphereGeom.cross, WithLp.ofLp_toLp, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    PiLp.neg_apply]
  constructor <;> ring

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_density_chain_rule_at (f : Kern) (D : Pt) (C : Charts) (hD : D ∈ LamC)
    (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1) (hC : IsChart D C)
    (t s : ℝ) (ht : t ∈ Set.Icc 0 C.TA) (hs : s ∈ Set.Icc 0 C.TB)
    (hx : inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1) :
    J f D C t s = -Q12 f D C t s + H f D C t s := by
  let U := u D C t
  let V := v D C s
  let x := inner ℝ U V
  let d := delta D C t s
  let A := inner ℝ (nAv D) (cross U V)
  let B := inner ℝ (nBv D) (cross U V)
  let L1 := inner ℝ (nAv D) V - ‖D‖/2*x
  let L2 := inner ℝ (nBv D) U - ‖D-e‖/2*x
  have hD0 : D ≠ 0 := by simpa using hoff 0
  have hDe : D ≠ e := by simpa using hoff 1
  have hDe0 : D-e ≠ 0 := sub_ne_zero.mpr hDe
  rcases hC with ⟨hEA,hEB,hrA,hrB,hTA,hTB,hTA2,hTB2,hArcA,hArcB,hdu,hdv⟩
  have hC' : IsChart D C := ⟨hEA,hEB,hrA,hrB,hTA,hTB,hTA2,hTB2,hArcA,hArcB,hdu,hdv⟩
  have hUm : U ∈ arcA D := by rw [hArcA]; exact ⟨t,ht,rfl⟩
  have hVm : V ∈ arcB D := by rw [hArcB]; exact ⟨s,hs,rfl⟩
  simp only [arcA, if_neg hD0, Set.mem_setOf_eq] at hUm
  simp only [arcB, if_neg hDe, Set.mem_setOf_eq, dist_eq_norm] at hVm
  obtain ⟨hnA,hnB,hgram,ha0,hb0,hla,hlb,hRC,hRC0,hSigma,hverts⟩ :=
    HardSphereB5.SphericalCrofton.Aux.Geom.sigma_gram_data D hD hoff
  have hUcap := hUm.1
  have hVcap := hVm.1
  rw [hSigma] at hUcap hVcap
  have hnU : ‖U‖ = 1 := hUcap.1
  have hnV : ‖V‖ = 1 := hVcap.1
  have hAu : inner ℝ (nAv D) U = ‖D‖/2 := by
    have hi := norm_add_sq_real D U
    rw [hnU, hUm.2] at hi
    have hiDU : inner ℝ D U = -‖D‖^2/2 := by nlinarith only [hi]
    rw [nAv, real_inner_smul_left, inner_neg_left, hiDU]
    field_simp [norm_ne_zero_iff.mpr hD0]
  have hBv : inner ℝ (nBv D) V = ‖D-e‖/2 := by
    have hvsum : D+V-e = (D-e)+V := by abel
    rw [hvsum] at hVm
    have hi := norm_add_sq_real (D-e) V
    rw [hnV,hVm.2] at hi
    have hiDV : inner ℝ (D-e) V = -‖D-e‖^2/2 := by nlinarith only [hi]
    have haxis : e-D = -(D-e) := by abel
    rw [nBv,haxis,real_inner_smul_left,inner_neg_left,hiDV]
    field_simp [norm_ne_zero_iff.mpr hDe0]
  have hbnd : ‖D‖ ≤ 1 ∧ ‖D-e‖ ≤ 1 := by
    simpa [LamC,Metric.mem_closedBall,dist_eq_norm] using hD
  have ha1 : ‖D‖/2 < 1 := by linarith [hbnd.1]
  have hb1 : ‖D-e‖/2 < 1 := by linarith [hbnd.2]
  have hcap := SphereGeom.Aux.Santalo.cap_density_algebra (nAv D) (nBv D) U V
    (‖D‖/2) (‖D-e‖/2) hnA hnB hnU hnV ha0 ha1 hb0 hb1 hAu hBv
    hVcap.2.1 hUcap.2.2 hx.1 hx.2
  have hRA : Real.sqrt (1-(‖D‖/2)^2) = rA D := by
    unfold rA; congr 1; ring
  have hRB : Real.sqrt (1-(‖D-e‖/2)^2) = rB D := by
    unfold rB; congr 1; ring
  have hDens : rA D*rB D*santaloDens U V (tanA D U) (tanB D V) =
      L1*L2/Real.sin d^3 := by
    simpa only [hRA,hRB,tanA,tanB,L1,L2,x,d,delta,U,V] using hcap.2.2.2.2
  have hJ : J f D C t s = cutKern f d * (L1*L2/Real.sin d^3) := by
    change rA D*rB D*(cutKern f d*santaloDens U V (tanA D U) (tanB D V)) = _
    calc
      _ = cutKern f d*(rA D*rB D*santaloDens U V (tanA D U) (tanB D V)) := by ring
      _ = _ := by rw [hDens]
  have hMix : -deriv (fun z => deriv (delta D C z) s) t = L1*L2/Real.sin d^3 := by
    simpa only [hAu,hBv,L1,L2,x,d,delta,U,V] using
      HardSphereB5.SphericalCrofton.Aux.Santalo.mixed_distance_identity D C hC' t s ht hs hx
  have htr := triples (nAv D) (nBv D) U V
  have hdT : deriv (fun z => delta D C z s) t = -A/Real.sin d := by
    have hdX := (hdu t).inner ℝ (hasDerivAt_const t V)
    have hd := (Real.hasDerivAt_arccos (ne_of_gt hx.1) (ne_of_lt hx.2)).comp t hdX
    change deriv (fun z => Real.arccos (inner ℝ (u D C z) V)) t = _
    simpa [Function.comp_def, htr.1, Real.sin_arccos, neg_div, div_eq_mul_inv,
      mul_comm, A,d,delta,U,V] using hd.deriv
  have hdS : deriv (delta D C t) s = -B/Real.sin d := by
    have hdX := (hasDerivAt_const s U).inner ℝ (hdv s)
    have hd := (Real.hasDerivAt_arccos (ne_of_gt hx.1) (ne_of_lt hx.2)).comp s hdX
    change deriv (fun z => Real.arccos (inner ℝ U (v D C z))) s = _
    simpa [Function.comp_def,htr.2,Real.sin_arccos,neg_div,div_eq_mul_inv,
      mul_comm,B,d,delta,U,V] using hd.deriv
  have hsinSq : Real.sin d^2 = 1-x^2 := by
    change Real.sin (Real.arccos x)^2 = _
    rw [Real.sin_arccos]
    exact Real.sq_sqrt (by nlinarith [hx.1,hx.2])
  have hcos : Real.cos d = x := Real.cos_arccos hx.1.le hx.2.le
  have hcut : d < π/3 ↔ 1/2 < x := by
    have hp : 0 < π/3 := by positivity
    have hp' : π/3 < π := by linarith [Real.pi_pos]
    have hdc : Real.cos (π/3) < Real.cos d ↔ d < π/3 :=
      Real.strictAntiOn_cos.lt_iff_gt
        ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
        ⟨Real.arccos_nonneg x,Real.arccos_le_pi x⟩
    simpa only [Real.cos_pi_div_three,hcos] using hdc.symm
  have hHp : H f D C t s = (if 1/2<x then rhoK f x*A*B else 0) := by
    change rA D*rB D*((if 1/2<x then rhoK f x*A*B else 0)/(rA D*rB D)) = _
    field_simp [ne_of_gt (mul_pos hrA hrB)]
  have hH : H f D C t s =
      (if d<π/3 then deriv (phiK f) d else 0)*
        deriv (fun z => delta D C z s) t * deriv (delta D C t) s := by
    rw [hHp,hdT,hdS]
    by_cases hc : d<π/3
    · rw [if_pos hc,if_pos (hcut.mp hc)]
      have hRho := HardSphereB5.SphericalCrofton.rho_rational f d
      rw [hcos,← hsinSq] at hRho
      rw [← hRho]
      ring
    · rw [if_neg hc,if_neg (fun hxx => hc (hcut.mpr hxx))]
      simp
  have hQ := HardSphereB5.SphericalCrofton.Aux.Santalo.mixed_primitive_chain f D C t s hx
  rw [hJ,hH,hQ]
  dsimp only [d] at hMix ⊢
  rw [← hMix]
  ring
