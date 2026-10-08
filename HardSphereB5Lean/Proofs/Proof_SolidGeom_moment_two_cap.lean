import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_pair_normal_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_twoBallSurface_capReduction
import HardSphereB5Lean.Theorems.Thm_SolidGeom_Q_positive_parameters
import HardSphereB5Lean.Theorems.Thm_SphereGeom_two_cap_frame_moment_closed
import HardSphereB5Lean.Theorems.Thm_SphereGeom_cross_vec_triple
set_option autoImplicit false
open MeasureTheory Real SphereGeom
set_option maxHeartbeats 1500000

theorem proof_SolidGeom_moment_two_cap (x y z : E3)
    (hQ : 0 < 4 * dist x y ^ 2 * dist x z ^ 2 - (dist x y ^ 2 + dist x z ^ 2 - dist y z ^ 2) ^ 2
        - dist x y ^ 2 * dist x z ^ 2 * dist y z ^ 2) :
    let a := dist x y ^ 2
    let b := dist x z ^ 2
    let cc := dist y z ^ 2
    let Δ := 4 * a * b - (a + b - cc) ^ 2
    let Q := Δ - a * b * cc
    ∫ u in Metric.closedBall y 1 ∩ Metric.closedBall z 1, (u - x) ∂(sphereMeasure x) =
      ((1 - a / 4) / √a * Complex.arg ⟨√a * (b + cc - a), 2 * √Q⟩) • (y - x)
        + ((1 - b / 4) / √b * Complex.arg ⟨√b * (a + cc - b), 2 * √Q⟩) • (z - x)
        + (√Q / Δ) • cross ((y - x) - (z - x)) (cross (y - x) (z - x))  := by
  classical
  let v := y-x
  let w := z-x
  let a := dist x y ^ 2
  let b := dist x z ^ 2
  let cc := dist y z ^ 2
  let D := 4*a*b-(a+b-cc)^2
  let Q := D-a*b*cc
  let A := ‖v‖
  let B := ‖w‖
  let p := inner ℝ v w
  have hva : A^2=a := by simp [A,v,a,dist_eq_norm, norm_sub_rev]
  have hwb : B^2=b := by simp [B,w,b,dist_eq_norm, norm_sub_rev]
  have hccp : cc=a+b-2*p := by
    have hh := norm_sub_sq_real v w
    have hdist : ‖v-w‖^2=cc := by
      have hvec : v-w=y-z := by dsimp [v,w]; abel
      rw [hvec]; simp [cc,dist_eq_norm]
    rw [hdist] at hh
    dsimp only [A,B,p] at hva hwb ⊢
    nlinarith
  have hpars := SolidGeom.Q_positive_parameters a b cc (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) hQ
  obtain ⟨hap,ha4,hbp,hb4,hcp,hc4,hDp⟩ := hpars
  have hA : 0<A := by have := norm_nonneg v; nlinarith
  have hB : 0<B := by have := norm_nonneg w; nlinarith
  have hA2 : A<2 := by nlinarith
  have hB2 : B<2 := by nlinarith
  have hG : 0 < ‖v‖^2*‖w‖^2-(inner ℝ v w)^2 := by
    change 0 < A^2*B^2-p^2
    have hd : D=4*(A^2*B^2-p^2) := by
      dsimp [D]
      rw [hccp,← hva,← hwb]
      ring
    have hpos : 0<D := hDp
    linarith
  obtain ⟨e,he,hv,hw⟩ := SphereGeom.exists_pair_normal_frame v w hG
  let K := p/A
  let L := sqrt (B^2-K^2)
  have hKA : K*A=p := by dsimp [K]; field_simp
  have hKAsq : A^2*K^2=p^2 := by nlinarith only [congrArg (fun t : ℝ => t^2) hKA]
  have hG' : 0<A^2*B^2-p^2 := hG
  have hLS : L^2=B^2-K^2 := by
    dsimp [L]
    apply sq_sqrt
    have : 0 < A^2*(B^2-K^2) := by nlinarith only [hG',hKAsq]
    nlinarith [sq_nonneg A]
  have hL : 0<L := by
    have : 0 < A^2*L^2 := by nlinarith only [hG',hKAsq,congrArg (fun t : ℝ => A^2*t) hLS]
    have hn : 0≤L := sqrt_nonneg _
    nlinarith [sq_nonneg A]
  have hsum : K^2+L^2=B^2 := by linarith
  have hw' : w=K • e 0+L • e 1 := hw
  have hcframe : cc=A^2+K^2+L^2-2*A*K := by nlinarith only [hccp,hva,hwb,hKA,hLS]
  let H := L^2*(1-A^2/4)-((K^2+L^2)/2-K*A/2)^2
  have hQH : Q=4*A^2*H := by
    dsimp only [Q,D]
    rw [← hva,← hwb,← hsum,hcframe]
    dsimp [H]
    ring
  have hH : 0<H := by
    have hq : 0<Q := hQ
    rw [hQH] at hq
    nlinarith [sq_nonneg A]
  have hsQ : sqrt Q=2*A*sqrt H := by
    rw [hQH]
    have hh : 4*A^2*H=(2*A)^2*H := by ring
    rw [hh,sqrt_mul (sq_nonneg _),sqrt_sq (by positivity)]
  have hD : D=4*A^2*L^2 := by
    dsimp [D]
    rw [← hva,← hwb,← hsum,hcframe]
    ring
  have hBsqrt : sqrt (K^2+L^2)=B := by rw [hsum,sqrt_sq hB.le]
  have hmoment := SphereGeom.two_cap_frame_moment_closed e he A K L hA hA2 hL
    (by nlinarith only [hsum,hwb,hb4]) hH
  dsimp only at hmoment
  rw [hBsqrt] at hmoment
  change (∫ u in cap (A • e 0) (A^2/2) ∩ cap (K • e 0+L • e 1) ((K^2+L^2)/2),u ∂dOmega) =
    ((1-A^2/4)*Complex.arg ⟨B^2-A*K,2*sqrt H⟩ +
      ((1-B^2/4)*K/B)*Complex.arg ⟨B*(A-K),2*sqrt H⟩-sqrt H/2) • e 0 +
    (((1-B^2/4)*L/B)*Complex.arg ⟨B*(A-K),2*sqrt H⟩-sqrt H*(A-K)/(2*L)) • e 1 at hmoment
  have hv' : v=A • e 0 := hv
  have hsa : sqrt a=A := by rw [← hva,sqrt_sq hA.le]
  have hsb : sqrt b=B := by rw [← hwb,sqrt_sq hB.le]
  have hcnorm : cc=A^2+B^2-2*A*K := by nlinarith only [hcframe,hsum]
  have hz0 : (⟨sqrt a*(b+cc-a),2*sqrt Q⟩ : ℂ) =
      ((2*A : ℝ) : ℂ) * ⟨B^2-A*K,2*sqrt H⟩ := by
    apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.re,Complex.im,zero_mul,mul_zero,sub_zero,add_zero]
    · rw [hsa,← hwb,← hva,hcnorm]; ring
    · rw [hsQ]; ring
  have hz1 : (⟨sqrt b*(a+cc-b),2*sqrt Q⟩ : ℂ) =
      ((2*A : ℝ) : ℂ) * ⟨B*(A-K),2*sqrt H⟩ := by
    apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.re,Complex.im,zero_mul,mul_zero,sub_zero,add_zero]
    · rw [hsb,← hwb,← hva,hcnorm]; ring
    · rw [hsQ]; ring
  have harg0 : Complex.arg ⟨sqrt a*(b+cc-a),2*sqrt Q⟩ =
      Complex.arg ⟨B^2-A*K,2*sqrt H⟩ := by rw [hz0,Complex.arg_real_mul _ (by positivity)]
  have harg1 : Complex.arg ⟨sqrt b*(a+cc-b),2*sqrt Q⟩ =
      Complex.arg ⟨B*(A-K),2*sqrt H⟩ := by rw [hz1,Complex.arg_real_mul _ (by positivity)]
  have hcross : cross (v-w) (cross v w)=(p-b) • v-(a-p) • w := by
    rw [SphereGeom.cross_vec_triple]
    congr 2
    · dsimp [p]
      rw [inner_sub_left,real_inner_self_eq_norm_sq]
      exact congrArg (fun t : ℝ => inner ℝ v w-t) hwb
    · dsimp [p]
      rw [inner_sub_right,real_inner_self_eq_norm_sq]
      exact congrArg (fun t : ℝ => t-inner ℝ v w) hva
  rw [(SphereGeom.twoBallSurface_capReduction x y z).2]
  change (∫ u in cap v (A^2/2) ∩ cap w (B^2/2),u ∂dOmega) =
    ((1-a/4)/sqrt a*Complex.arg ⟨sqrt a*(b+cc-a),2*sqrt Q⟩) • v +
    ((1-b/4)/sqrt b*Complex.arg ⟨sqrt b*(a+cc-b),2*sqrt Q⟩) • w +
    (sqrt Q/D) • cross (v-w) (cross v w)
  rw [harg0,harg1,hsa,hsb,hsQ,hD,hcross]
  rw [hv',hw',← hsum]
  rw [hmoment]
  simp only [← hva,← hwb,hv',hw',smul_add,smul_sub,smul_smul]
  rw [hsum,← hKA]
  ext i
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp [ne_of_gt hA,ne_of_gt hB,ne_of_gt hL]
  rw [← hsum]
  ring
