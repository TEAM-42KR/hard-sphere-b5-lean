import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_areaPrimitive
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SolidGeom.CapPolar
set_option maxHeartbeats 2000000

private theorem S2_azimuth_deriv (A ψ:ℝ) (hA:0<A):
    HasDerivAt (continuousAzimuth A) (A/((Real.cos ψ)^2+A^2*(Real.sin ψ)^2)) ψ:=by
  let s:=Real.sin ψ
  let c:=Real.cos ψ
  let N:ℝ:=(1-A)*s*c
  let Q:ℝ:=c^2+A*s^2
  let D:ℝ:=c^2+A^2*s^2
  have hsc:s^2+c^2=1:=Real.sin_sq_add_cos_sq ψ
  have hq:0<Q:=by
    dsimp[Q]
    by_cases hs:s=0
    · simp only[hs,zero_pow (by norm_num:2≠0),mul_zero,add_zero]
      nlinarith
    · have hs2:0<s^2:=sq_pos_of_ne_zero hs
      nlinarith[sq_nonneg c,mul_pos hA hs2]
  have hd:0<D:=by
    dsimp[D]
    by_cases hs:s=0
    · simp only[hs,zero_pow (by norm_num:2≠0),mul_zero,add_zero]
      nlinarith
    · nlinarith[sq_nonneg c,mul_pos (sq_pos_of_pos hA) (sq_pos_of_ne_zero hs)]
  have hnq:Q^2+N^2=D:=by
    calc _=(s^2+c^2)*D:=by dsimp[Q,N,D];ring
         _=D:=by rw[hsc,one_mul]
  have hdelta:(1-A)*(c^2-s^2)*Q-N*(2*(A-1)*s*c)=D-A:=by
    calc _=(1-A)*(s^2+c^2)*(c^2-A*s^2):=by dsimp[Q,N];ring
         _=(1-A)*(c^2-A*s^2):=by rw[hsc,mul_one]
         _=D-A:=by dsimp[D];nlinarith[hsc]
  have hN:HasDerivAt (fun x:ℝ=>(1-A)*Real.sin x*Real.cos x)
      ((1-A)*(c^2-s^2)) ψ:=by
    have h0:=(((hasDerivAt_sin ψ).const_mul (1-A)).mul (hasDerivAt_cos ψ))
    apply h0.congr_deriv
    dsimp[s,c]
    ring
  have hQ:HasDerivAt (fun x:ℝ=>(Real.cos x)^2+A*(Real.sin x)^2)
      (2*(A-1)*s*c) ψ:=by
    have h0:=((hasDerivAt_cos ψ).pow 2).add (((hasDerivAt_sin ψ).pow 2).const_mul A)
    apply h0.congr_deriv
    dsimp[s,c]
    ring
  have h0:=(hasDerivAt_id ψ).sub ((hN.div hQ hq.ne').arctan)
  change HasDerivAt (continuousAzimuth A)
    (1-(1/(1+(N/Q)^2))*(((1-A)*(c^2-s^2)*Q-N*(2*(A-1)*s*c))/Q^2)) ψ at h0
  have he:1-(1/(1+(N/Q)^2))*(((1-A)*(c^2-s^2)*Q-N*(2*(A-1)*s*c))/Q^2)=A/D:=by
    rw[hdelta]
    have hr:0<1+(N/Q)^2:=by positivity
    field_simp [hq.ne',hd.ne',hr.ne']
    nlinarith[hnq]
  exact h0.congr_deriv he

private theorem S2_tail_deriv (h k t:ℝ) (hk:0<k) (hkh:h^2+k^2=1) (ht:t^2<k^2):
    HasDerivAt (tailPrimitive h k) (Real.sqrt (k^2-t^2)/(1-t^2)) t:=by
  let R:=Real.sqrt (k^2-t^2)
  have hr:0<R:=Real.sqrt_pos.mpr (sub_pos.mpr ht)
  have hr2:R^2=k^2-t^2:=Real.sq_sqrt (sub_nonneg.mpr ht.le)
  have h1:0<1-t^2:=by nlinarith[sq_nonneg h]
  have hlt:(t/k)^2<1:=by
    rw[div_pow,div_lt_one (sq_pos_of_pos hk)]
    exact ht
  have hm:t/k≠-1:=by intro he;rw[he] at hlt;norm_num at hlt
  have hp:t/k≠1:=by intro he;rw[he] at hlt;norm_num at hlt
  have has:HasDerivAt (fun x:ℝ=>Real.arcsin (x/k))
      ((1/Real.sqrt (1-(t/k)^2))*(1/k)) t:=by
    simpa only[Function.comp_def,id_eq] using
      (Real.hasDerivAt_arcsin (x:=t/k) hm hp).comp t ((hasDerivAt_id t).div_const k)
  have hroot:Real.sqrt (1-(t/k)^2)=R/k:=by
    have hp0:0≤1-(t/k)^2:=sub_nonneg.mpr hlt.le
    have hRk:0≤R/k:=div_nonneg hr.le hk.le
    have he:(R/k)^2=1-(t/k)^2:=by
      field_simp[hk.ne']
      nlinarith[hr2]
    nlinarith[Real.sq_sqrt hp0,he,Real.sqrt_nonneg (1-(t/k)^2)]
  have has':HasDerivAt (fun x:ℝ=>Real.arcsin (x/k)) (1/R) t:=by
    convert has using 1
    rw[hroot]
    field_simp[hr.ne',hk.ne']
  have hdR:HasDerivAt (fun x:ℝ=>Real.sqrt (k^2-x^2)) (-t/R) t:=by
    have h0:=((hasDerivAt_const t (k^2)).sub ((hasDerivAt_id t).pow 2)).sqrt (sub_pos.mpr ht).ne'
    apply h0.congr_deriv
    dsimp[R]
    field_simp
    <;>ring
  have hat:HasDerivAt (fun x:ℝ=>h*Real.arctan (h*x/Real.sqrt (k^2-x^2)))
      (h*((1/(1+(h*t/R)^2))*((h*R-h*t*(-t/R))/R^2))) t:=by
    have h0:=((((hasDerivAt_id t).const_mul h).div hdR hr.ne').arctan).const_mul h
    simpa only[mul_one,id_eq,Function.comp_def,Pi.div_apply] using h0
  have he:1/R-h*((1/(1+(h*t/R)^2))*((h*R-h*t*(-t/R))/R^2))=R/(1-t^2):=by
    have hden:0<1+(h*t/R)^2:=by positivity
    field_simp[hr.ne',h1.ne',hden.ne']
    nlinarith[hr2,hkh]
  have hd:=has'.sub hat
  change HasDerivAt (tailPrimitive h k)
    (1/R-h*((1/(1+(h*t/R)^2))*((h*R-h*t*(-t/R))/R^2))) t at hd
  exact hd.congr_deriv he

private theorem S2_bounds (A h ψ:ℝ) (hh:0<h) (hA:h<A) (hA1:A≤1):
    (capBeta A)^2=1-A^2 ∧ (capK h)^2=1-h^2 ∧ 0<capK h ∧
    (capBeta A*Real.sin ψ)^2<(capK h)^2 ∧ 0<rayDenom A ψ:=by
  have hA0:0<A:=hh.trans hA
  have hh1:h<1:=hA.trans_le hA1
  have ha:0≤1-A^2:=by nlinarith
  have hk:0<1-h^2:=by nlinarith
  have hβ:(capBeta A)^2=1-A^2:=Real.sq_sqrt ha
  have hk2:(capK h)^2=1-h^2:=Real.sq_sqrt hk.le
  have hs:(Real.sin ψ)^2≤1:=by nlinarith[Real.sin_sq_add_cos_sq ψ,sq_nonneg (Real.cos ψ)]
  have ht:(capBeta A*Real.sin ψ)^2≤(capBeta A)^2:=by
    rw[mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) hs
  have hlt:(capBeta A*Real.sin ψ)^2<(capK h)^2:=by nlinarith
  refine ⟨hβ,hk2,Real.sqrt_pos.mpr hk,hlt,?_⟩
  unfold rayDenom
  rw[←mul_pow]
  nlinarith[sq_nonneg h]

private theorem S2_area_deriv (A h ψ:ℝ) (hh:0<h) (hA:h<A) (hA1:A≤1):
    HasDerivAt (areaPrimitive A h) (areaDensity A h ψ) ψ:=by
  obtain ⟨hβ,hk2,hk,ht,hden⟩:=S2_bounds A h ψ hh hA hA1
  have hA0:0<A:=hh.trans hA
  have hd:(Real.cos ψ)^2+A^2*(Real.sin ψ)^2=rayDenom A ψ:=by
    unfold rayDenom
    rw[hβ]
    nlinarith[Real.sin_sq_add_cos_sq ψ]
  have haz:HasDerivAt (continuousAzimuth A) (A/rayDenom A ψ) ψ:=by
    simpa only[hd] using S2_azimuth_deriv A ψ hA0
  have ht0:=S2_tail_deriv h (capK h) (capBeta A*Real.sin ψ) hk (by nlinarith) ht
  have hsin:= (hasDerivAt_sin ψ).const_mul (capBeta A)
  have hcomp:=ht0.comp ψ hsin
  have raw:=((hasDerivAt_id ψ).sub (haz.const_mul h)).add hcomp
  change HasDerivAt (areaPrimitive A h)
    (1-h*(A/rayDenom A ψ)+(Real.sqrt ((capK h)^2-(capBeta A*Real.sin ψ)^2)/
      (1-(capBeta A*Real.sin ψ)^2))*(capBeta A*Real.cos ψ)) ψ at raw
  apply raw.congr_deriv
  unfold areaDensity exitCos rayRadical rayDenom
  rw[mul_pow]
  field_simp
  <;>ring

private theorem S2_density_continuous (A h:ℝ) (hh:0<h) (hA:h<A) (hA1:A≤1):
    Continuous (areaDensity A h):=by
  have hd:∀ψ,rayDenom A ψ≠0:=fun ψ=>(S2_bounds A h ψ hh hA hA1).2.2.2.2.ne'
  unfold areaDensity exitCos rayRadical rayDenom
  apply continuous_const.sub
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact hd

theorem proof_SolidGeom_CapPolar_sector_area_primitive (A h a b:ℝ) (hh:0<h) (hA:h<A) (hA1:A≤1):
    (∫ψ in a..b,areaDensity A h ψ)=areaPrimitive A h b-areaPrimitive A h a:=by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ψ _=>S2_area_deriv A h ψ hh hA hA1)
    ((S2_density_continuous A h hh hA hA1).intervalIntegrable a b)
#print axioms proof_SolidGeom_CapPolar_sector_area_primitive
