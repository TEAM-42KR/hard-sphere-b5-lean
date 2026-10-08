import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_momentPrimitive
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
set_option maxHeartbeats 1600000

private lemma S3_beta_sq (A h : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    capBeta A^2=1-A^2 := Real.sq_sqrt (by nlinarith)
private lemma S3_k_sq (A h : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    capK h^2=1-h^2 := Real.sq_sqrt (by nlinarith)
private lemma S3_denom_eq (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    rayDenom A ψ=A^2+(capBeta A*Real.cos ψ)^2 := by
  unfold rayDenom
  nlinarith [S3_beta_sq A h hh hA hA1,
    congrArg (fun z : ℝ => capBeta A^2*z) (Real.sin_sq_add_cos_sq ψ)]
private lemma S3_denom_pos (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    0<rayDenom A ψ := by
  rw [S3_denom_eq A h ψ hh hA hA1]
  nlinarith [sq_nonneg (capBeta A*Real.cos ψ)]
private lemma S3_radical_pos (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    0<rayRadical A h ψ := by
  unfold rayRadical
  apply Real.sqrt_pos.mpr
  rw [S3_k_sq A h hh hA hA1]
  rw [show 1-h^2-capBeta A^2*Real.sin ψ^2=rayDenom A ψ-h^2 by unfold rayDenom; ring]
  rw [S3_denom_eq A h ψ hh hA hA1]
  nlinarith [sq_nonneg (capBeta A*Real.cos ψ)]
private lemma S3_radical_sq (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    rayRadical A h ψ^2=rayDenom A ψ-h^2 := by
  unfold rayRadical
  rw [Real.sq_sqrt (Real.sqrt_pos.mp (S3_radical_pos A h ψ hh hA hA1)).le]
  rw [S3_k_sq A h hh hA hA1]
  unfold rayDenom
  ring
private lemma S3_CS_unit (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    exitCos A h ψ^2+exitSin A h ψ^2=1 := by
  have hD := (S3_denom_pos A h ψ hh hA hA1).ne'
  unfold exitCos exitSin
  rw [div_pow,div_pow,← add_div]
  apply (div_eq_one_iff_eq (pow_ne_zero 2 hD)).2
  calc
    _ = (A^2+(capBeta A*Real.cos ψ)^2)*(h^2+rayRadical A h ψ^2) := by ring
    _ = rayDenom A ψ^2 := by
      rw [← S3_denom_eq A h ψ hh hA hA1,S3_radical_sq A h ψ hh hA hA1]
      ring
private lemma S3_CS_exit (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    A*exitCos A h ψ+capBeta A*Real.cos ψ*exitSin A h ψ=h ∧
    A*exitSin A h ψ-capBeta A*Real.cos ψ*exitCos A h ψ=rayRadical A h ψ := by
  have hD := (S3_denom_pos A h ψ hh hA hA1).ne'
  unfold exitCos exitSin
  constructor <;> field_simp [hD] <;> rw [S3_denom_eq A h ψ hh hA hA1] <;> ring
private lemma S3_S_pos (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    0<exitSin A h ψ := by
  have hp := S3_radical_pos A h ψ hh hA hA1
  have hD := S3_denom_pos A h ψ hh hA hA1
  have ha : 0<A := lt_trans hh hA
  have he : (A*rayRadical A h ψ)^2-(capBeta A*h*Real.cos ψ)^2 =
      rayDenom A ψ*(A^2-h^2) := by
    rw [mul_pow,S3_radical_sq A h ψ hh hA hA1,S3_denom_eq A h ψ hh hA hA1]
    ring
  have hpos : 0<rayDenom A ψ*(A^2-h^2) := mul_pos hD (by nlinarith)
  unfold exitSin
  apply div_pos _ hD
  nlinarith [mul_pos ha hp]
private lemma S3_C_bound (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    |exitCos A h ψ|<1 := by
  have hcs := S3_CS_unit A h ψ hh hA hA1
  have hs := S3_S_pos A h ψ hh hA hA1
  rw [abs_lt]
  constructor <;> nlinarith [sq_pos_of_pos hs]
private lemma S3_radius_trig (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    Real.cos (exitRadius A h ψ)=exitCos A h ψ ∧
    Real.sin (exitRadius A h ψ)=exitSin A h ψ := by
  have hC := S3_C_bound A h ψ hh hA hA1
  constructor
  · exact Real.cos_arccos (abs_lt.mp hC).1.le (abs_lt.mp hC).2.le
  · unfold exitRadius
    rw [Real.sin_arccos]
    have he : 1-exitCos A h ψ^2=exitSin A h ψ^2 := by
      linarith [S3_CS_unit A h ψ hh hA hA1]
    rw [he,Real.sqrt_sq_eq_abs,abs_of_pos (S3_S_pos A h ψ hh hA hA1)]
private lemma S3_radius_differentiable (A h : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    Differentiable ℝ (exitRadius A h) := by
  intro ψ
  have hC := S3_C_bound A h ψ hh hA hA1
  unfold exitRadius
  apply (Real.differentiableAt_arccos.mpr ⟨ne_of_gt (abs_lt.mp hC).1,ne_of_lt (abs_lt.mp hC).2⟩).comp
  unfold exitCos rayRadical rayDenom
  fun_prop (disch := first | exact (S3_denom_pos A h ψ hh hA hA1).ne' |
    exact (show capK h^2-capBeta A^2*Real.sin ψ^2≠0 from
      (Real.sqrt_pos.mp (S3_radical_pos A h ψ hh hA hA1)).ne'))
private lemma S3_radius_hasDerivAt (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    HasDerivAt (exitRadius A h) (-capBeta A*Real.sin ψ*exitSin A h ψ/rayRadical A h ψ) ψ := by
  have hd := (S3_radius_differentiable A h hh hA hA1 ψ).hasDerivAt
  have he : (fun s => A*Real.cos (exitRadius A h s)+capBeta A*Real.cos s*Real.sin (exitRadius A h s)) =
      fun _ => h := by
    funext s
    rw [(S3_radius_trig A h s hh hA hA1).1,(S3_radius_trig A h s hh hA hA1).2]
    exact (S3_CS_exit A h s hh hA hA1).1
  have hdiff := (hd.cos.const_mul A).add (((hasDerivAt_cos ψ).const_mul (capBeta A)).mul hd.sin)
  change HasDerivAt (fun s => A*Real.cos (exitRadius A h s)+
    capBeta A*Real.cos s*Real.sin (exitRadius A h s)) _ ψ at hdiff
  rw [he] at hdiff
  have hz := hdiff.unique (hasDerivAt_const ψ h)
  rw [(S3_radius_trig A h ψ hh hA hA1).1,(S3_radius_trig A h ψ hh hA hA1).2] at hz
  have hR := (S3_CS_exit A h ψ hh hA hA1).2
  have hRp := (S3_radical_pos A h ψ hh hA hA1).ne'
  have hg : deriv (exitRadius A h) ψ*rayRadical A h ψ =
      -capBeta A*Real.sin ψ*exitSin A h ψ := by
    linear_combination -hz-(deriv (exitRadius A h) ψ)*hR
  have heder : deriv (exitRadius A h) ψ = -capBeta A*Real.sin ψ*exitSin A h ψ/rayRadical A h ψ :=
    (eq_div_iff hRp).mpr hg
  rw [heder] at hd
  exact hd

private lemma S3_atan_quotient_algebra (x n xp np : ℝ) (hx : x≠0) :
    (1/(1+(n/x)^2))*((np*x-n*xp)/x^2)=(np*x-n*xp)/(x^2+n^2) := by
  have hd : x^2+n^2≠0 := by nlinarith [sq_pos_of_ne_zero hx,sq_nonneg n]
  have ht : 1+(n/x)^2≠0 := by positivity
  field_simp [hx,hd,ht]
  <;> ring

private lemma S3_contAz_hasDerivAt (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    HasDerivAt (continuousAzimuth A) (A/rayDenom A ψ) ψ := by
  let T := Real.cos ψ^2+A*Real.sin ψ^2
  let N := (1-A)*Real.sin ψ*Real.cos ψ
  let Tp := 2*Real.cos ψ*(-Real.sin ψ)+A*(2*Real.sin ψ*Real.cos ψ)
  let Np := (1-A)*Real.cos ψ*Real.cos ψ+(1-A)*Real.sin ψ*(-Real.sin ψ)
  have hT : 0<T := by dsimp [T]; nlinarith [Real.sin_sq_add_cos_sq ψ,sq_nonneg (Real.cos ψ),sq_nonneg (Real.sin ψ)]
  have hN := ((hasDerivAt_sin ψ).const_mul (1-A)).mul (hasDerivAt_cos ψ)
  have hDen := ((hasDerivAt_cos ψ).pow 2).add (((hasDerivAt_sin ψ).pow 2).const_mul A)
  have hAt := (hN.div hDen hT.ne').arctan
  have hs := (hasDerivAt_id ψ).sub hAt
  unfold continuousAzimuth
  apply hs.congr_deriv
  simp only [Nat.reduceSub,pow_one,Nat.cast_ofNat]
  change 1-(1/(1+(N/T)^2))*((Np*T-N*Tp)/T^2)=A/rayDenom A ψ
  rw [S3_atan_quotient_algebra T N Tp Np hT.ne']
  have hc := Real.sin_sq_add_cos_sq ψ
  have he : T^2+N^2=rayDenom A ψ := by
    calc
      _ = (Real.cos ψ^2+Real.sin ψ^2)*(Real.cos ψ^2+A^2*Real.sin ψ^2) := by dsimp [T,N]; ring
      _ = _ := by
        rw [show Real.cos ψ^2+Real.sin ψ^2=1 by nlinarith [hc]]
        unfold rayDenom
        rw [S3_beta_sq A h hh hA hA1]
        nlinarith [hc]
  have hnum : T^2+N^2-(Np*T-N*Tp)=A := by
    calc
      _ = A*(Real.cos ψ^2+Real.sin ψ^2)^2 := by dsimp [T,N,Tp,Np]; ring
      _ = _ := by rw [show Real.cos ψ^2+Real.sin ψ^2=1 by nlinarith [hc]]; ring
  rw [he]
  have hn : Np*T-N*Tp=rayDenom A ψ-A := by rw [he] at hnum; linarith
  rw [hn]
  field_simp [(S3_denom_pos A h ψ hh hA hA1).ne']
  <;> ring

private lemma S3_az_tail_hasDerivAt (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    HasDerivAt (fun s => Real.arctan (h*capBeta A*Real.sin s/rayRadical A h s))
      (h*capBeta A*Real.cos ψ/(rayDenom A ψ*rayRadical A h ψ)) ψ := by
  have hp := S3_radical_pos A h ψ hh hA hA1
  have hd := S3_denom_pos A h ψ hh hA hA1
  have hr := S3_radical_sq A h ψ hh hA hA1
  have hR := (((hasDerivAt_sin ψ).pow 2).const_mul (capBeta A^2)).const_sub (capK h^2)
  have hRs := hR.sqrt (Real.sqrt_pos.mp hp).ne'
  have hRs' : HasDerivAt (rayRadical A h)
      (-capBeta A^2*Real.sin ψ*Real.cos ψ/rayRadical A h ψ) ψ := by
    apply hRs.congr_deriv
    simp only [Nat.reduceSub,pow_one,Nat.cast_ofNat]
    change -(capBeta A^2*(2*Real.sin ψ*Real.cos ψ))/(2*rayRadical A h ψ) = _
    field_simp [hp.ne']
    <;> ring
  have hQ := ((hasDerivAt_sin ψ).const_mul (h*capBeta A)).div hRs' hp.ne'
  apply hQ.arctan.congr_deriv
  change (1/(1+(h*capBeta A*Real.sin ψ/rayRadical A h ψ)^2))*
    ((h*capBeta A*Real.cos ψ*rayRadical A h ψ-
      h*capBeta A*Real.sin ψ*(-capBeta A^2*Real.sin ψ*Real.cos ψ/rayRadical A h ψ))/
      rayRadical A h ψ^2) = _
  rw [S3_atan_quotient_algebra _ _ _ _ hp.ne']
  have he : rayRadical A h ψ^2+(h*capBeta A*Real.sin ψ)^2 =
      (1-h^2)*rayDenom A ψ := by rw [hr]; unfold rayDenom; ring
  have hnum : h*capBeta A*Real.cos ψ*rayRadical A h ψ-
      h*capBeta A*Real.sin ψ*(-capBeta A^2*Real.sin ψ*Real.cos ψ/rayRadical A h ψ) =
      h*capBeta A*Real.cos ψ*(1-h^2)/rayRadical A h ψ := by
    field_simp [hp.ne']
    rw [hr]
    unfold rayDenom
    ring
  rw [he,hnum]
  have hk : 1-h^2≠0 := by nlinarith
  field_simp [hp.ne',hd.ne',hk]
  <;> ring

private lemma S3_azimuth_hasDerivAt (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    HasDerivAt (momentAzimuth A h) (exitSin A h ψ/rayRadical A h ψ) ψ := by
  have hd := (S3_contAz_hasDerivAt A h ψ hh hA hA1).add (S3_az_tail_hasDerivAt A h ψ hh hA hA1)
  apply hd.congr_deriv
  unfold exitSin
  field_simp [(S3_denom_pos A h ψ hh hA hA1).ne',(S3_radical_pos A h ψ hh hA hA1).ne']
  ring
private lemma S3_component_algebra (A B C S T V H R : ℝ)
    (hAB : A^2+B^2=1) (hCS : C^2+S^2=1) (hTV : T^2+V^2=1)
    (hH : A*C+B*V*S=H) (hR : A*S-B*V*C=R) :
    ((1-H^2)*A*S-H*B^2*C*T^2*S+H*B*S*V*R=S^2*R) ∧
    ((1-H^2)*B*S+H*A*B*C*T^2*S-H*A*S*V*R-B*T^2*S+S*C*V*R=0) ∧
    (H*(-A*B*C*T*S*V-A*S*T*R-B^2*T*S^2)+B*T*S*V+T*S*C*R=0) := by
  rw [← hH,← hR]
  constructor
  · linear_combination
      (-C*S*(A*C+B*S*V))*hAB +
      (-A*S*(B^2*T^2+B^2*V^2-B^2+1))*hCS +
      (B^2*S*(A*S^2-A-B*C*S*V))*hTV
  constructor
  · linear_combination
      (-S*(A*C*S*V-B*C^2*T^2-B*C^2*V^2+B*C^2+B*S^2*V^2))*hAB +
      (-B*S*(B^2*T^2+B^2*V^2-B^2-T^2+1))*hCS +
      (B*S*(A*B*C*S*V+B^2*S^2-B^2-S^2))*hTV
  · linear_combination (-S^2*T*(A*C+B*S*V))*hAB + (-B*S*T*V)*hCS

private lemma S3_moment_hasDerivAt (p a b : E3) (A h ψ : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    HasDerivAt (momentPrimitive p a b A h)
      ((exitSin A h ψ^2/2) • p +
        ((exitRadius A h ψ-exitSin A h ψ*exitCos A h ψ)/2) •
          (Real.cos ψ • a+Real.sin ψ • b)) ψ := by
  let C := exitCos A h ψ
  let S := exitSin A h ψ
  let T := Real.sin ψ
  let V := Real.cos ψ
  let β := capBeta A
  let R := rayRadical A h ψ
  let ρ := exitRadius A h ψ
  have hp : R≠0 := (S3_radical_pos A h ψ hh hA hA1).ne'
  have hr := S3_radius_hasDerivAt A h ψ hh hA hA1
  have hφ := S3_azimuth_hasDerivAt A h ψ hh hA hA1
  have hC : HasDerivAt (exitCos A h) (-S*(-β*T*S/R)) ψ := by
    have H := hr.cos
    have he : (fun s => Real.cos (exitRadius A h s))=exitCos A h :=
      funext (fun s => (S3_radius_trig A h s hh hA hA1).1)
    rw [he] at H
    rw [(S3_radius_trig A h ψ hh hA hA1).2] at H
    exact H
  have hS : HasDerivAt (exitSin A h) (C*(-β*T*S/R)) ψ := by
    have H := hr.sin
    have he : (fun s => Real.sin (exitRadius A h s))=exitSin A h :=
      funext (fun s => (S3_radius_trig A h s hh hA hA1).2)
    rw [he] at H
    rw [(S3_radius_trig A h ψ hh hA hA1).1] at H
    exact H
  have hSS := hS.mul (hasDerivAt_sin ψ)
  have hSC := hS.mul (hasDerivAt_cos ψ)
  have hP := ((hφ.const_mul ((1-h^2)*A)).add (hSS.const_mul (h*β))).div_const 2
  have hA' := (((hφ.const_mul ((1-h^2)*β)).sub (hSS.const_mul (h*A))).add
      (hr.mul (hasDerivAt_sin ψ))).div_const 2
  have hB := (((hSC.const_mul A).sub (hC.const_mul β)).const_mul h).sub
      (hr.mul (hasDerivAt_cos ψ)) |>.div_const 2
  have hd := ((hP.smul_const p).add (hA'.smul_const a)).add (hB.smul_const b)
  change HasDerivAt (fun y =>
    (((1-h^2)*A*momentAzimuth A h y+h*β*(exitSin A h y*Real.sin y))/2) • p +
    ((((1-h^2)*β*momentAzimuth A h y-h*A*(exitSin A h y*Real.sin y))+
      exitRadius A h y*Real.sin y)/2) • a +
    ((h*(A*(exitSin A h y*Real.cos y)-β*exitCos A h y)-exitRadius A h y*Real.cos y)/2) • b) _ ψ at hd
  have hefun : (fun y =>
    (((1-h^2)*A*momentAzimuth A h y+h*β*(exitSin A h y*Real.sin y))/2) • p +
    ((((1-h^2)*β*momentAzimuth A h y-h*A*(exitSin A h y*Real.sin y))+
      exitRadius A h y*Real.sin y)/2) • a +
    ((h*(A*(exitSin A h y*Real.cos y)-β*exitCos A h y)-exitRadius A h y*Real.cos y)/2) • b) =
      momentPrimitive p a b A h := by
    funext y
    dsimp [momentPrimitive,β]
    module
  rw [hefun] at hd
  have heq := S3_component_algebra A β C S T V h R
    (by dsimp [β]; nlinarith [S3_beta_sq A h hh hA hA1])
    (S3_CS_unit A h ψ hh hA hA1) (Real.sin_sq_add_cos_sq ψ)
    (S3_CS_exit A h ψ hh hA hA1).1 (S3_CS_exit A h ψ hh hA hA1).2
  apply hd.congr_deriv
  have h1 : ((1-h^2)*A*(S/R)+h*β*(C*(-β*T*S/R)*T+S*V))/2=S^2/2 := by
    field_simp [hp]
    nlinarith [heq.1]
  have h2 : (((1-h^2)*β*(S/R)-h*A*(C*(-β*T*S/R)*T+S*V))+
      ((-β*T*S/R)*T+ρ*V))/2 = ((ρ-S*C)/2)*V := by
    field_simp [hp]
    nlinarith [heq.2.1]
  have h3 : (h*(A*(C*(-β*T*S/R)*V+S*(-T))-β*(-S*(-β*T*S/R)))-
      ((-β*T*S/R)*V+ρ*(-T)))/2 = ((ρ-S*C)/2)*T := by
    field_simp [hp]
    nlinarith [heq.2.2]
  change (((1-h^2)*A*(S/R)+h*β*(C*(-β*T*S/R)*T+S*V))/2) • p +
    ((((1-h^2)*β*(S/R)-h*A*(C*(-β*T*S/R)*T+S*V))+((-β*T*S/R)*T+ρ*V))/2) • a +
    ((h*(A*(C*(-β*T*S/R)*V+S*(-T))-β*(-S*(-β*T*S/R)))-((-β*T*S/R)*V+ρ*(-T)))/2) • b = _
  rw [h1,h2,h3]
  module
private def S3_radialPrimitive (p a b : E3) (ψ ρ : ℝ) : E3 :=
  (Real.sin ρ^2/2) • p + ((ρ-Real.sin ρ*Real.cos ρ)/2) •
    (Real.cos ψ • a+Real.sin ψ • b)

private lemma S3_radial_hasDerivAt (p a b : E3) (ψ ρ : ℝ) :
    HasDerivAt (S3_radialPrimitive p a b ψ)
      (Real.sin ρ • polarRay p a b ψ ρ) ρ := by
  have hP := ((hasDerivAt_sin ρ).pow 2).div_const 2
  have hQ := ((hasDerivAt_id ρ).sub ((hasDerivAt_sin ρ).mul (hasDerivAt_cos ρ))).div_const 2
  have hd := (hP.smul_const p).add (hQ.smul_const (Real.cos ψ • a+Real.sin ψ • b))
  apply hd.congr_deriv
  have hc := Real.sin_sq_add_cos_sq ρ
  have hs : (1-(Real.cos ρ*Real.cos ρ+Real.sin ρ*(-Real.sin ρ)))/2=Real.sin ρ^2 := by nlinarith
  simp only [Nat.reduceSub,pow_one,Nat.cast_ofNat]
  rw [hs]
  unfold polarRay
  module

private lemma S3_radial_integral (p a b : E3) (A h ψ : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    (∫ ρ in (0)..(exitRadius A h ψ), Real.sin ρ • polarRay p a b ψ ρ) =
      (exitSin A h ψ^2/2) • p +
        ((exitRadius A h ψ-exitSin A h ψ*exitCos A h ψ)/2) •
          (Real.cos ψ • a+Real.sin ψ • b) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ρ hρ => S3_radial_hasDerivAt p a b ψ ρ)
    (show IntervalIntegrable (fun ρ => Real.sin ρ • polarRay p a b ψ ρ) volume 0 (exitRadius A h ψ) by
      apply Continuous.intervalIntegrable
      unfold polarRay
      fun_prop)
  rw [hi]
  simp only [S3_radialPrimitive,Real.sin_zero,Real.cos_zero,zero_pow (by norm_num : (2:ℕ)≠0),
    zero_div,zero_mul,sub_self,zero_smul,zero_add,sub_zero]
  rw [(S3_radius_trig A h ψ hh hA hA1).1,(S3_radius_trig A h ψ hh hA hA1).2]

private lemma S3_ray_density_continuous (p a b : E3) (A h : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    Continuous (fun ψ => (exitSin A h ψ^2/2) • p +
      ((exitRadius A h ψ-exitSin A h ψ*exitCos A h ψ)/2) •
        (Real.cos ψ • a+Real.sin ψ • b)) := by
  have hr : Continuous (exitRadius A h) := (S3_radius_differentiable A h hh hA hA1).continuous
  have hc : Continuous (exitCos A h) := by
    have he : exitCos A h = fun ψ => Real.cos (exitRadius A h ψ) :=
      funext (fun ψ => (S3_radius_trig A h ψ hh hA hA1).1.symm)
    rw [he]
    fun_prop
  have hs : Continuous (exitSin A h) := by
    have he : exitSin A h = fun ψ => Real.sin (exitRadius A h ψ) :=
      funext (fun ψ => (S3_radius_trig A h ψ hh hA hA1).2.symm)
    rw [he]
    fun_prop
  fun_prop

theorem proof_SolidGeom_CapPolar_sector_moment_primitive (p a b : SphereGeom.E3)
  (A h ψ₁ ψ₂ : ℝ) (hh : 0 < h) (hA : h < A) (hA1 : A ≤ 1)
  (hframe : Orthonormal ℝ (fun k : Fin 3 => ![p,a,b] k)) :
  (∫ ψ in ψ₁..ψ₂, ∫ ρ in (0)..(SolidGeom.CapPolar.exitRadius A h ψ),
    Real.sin ρ • SolidGeom.CapPolar.polarRay p a b ψ ρ) =
  SolidGeom.CapPolar.momentPrimitive p a b A h ψ₂ -
    SolidGeom.CapPolar.momentPrimitive p a b A h ψ₁  := by
  have hi : (∫ ψ in ψ₁..ψ₂, ∫ ρ in (0)..(exitRadius A h ψ),
      Real.sin ρ • polarRay p a b ψ ρ) =
      ∫ ψ in ψ₁..ψ₂, (exitSin A h ψ^2/2) • p +
        ((exitRadius A h ψ-exitSin A h ψ*exitCos A h ψ)/2) •
          (Real.cos ψ • a+Real.sin ψ • b) := by
    apply intervalIntegral.integral_congr
    intro ψ hψ
    exact S3_radial_integral p a b A h ψ hh hA hA1
  rw [hi]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ψ hψ => S3_moment_hasDerivAt p a b A h ψ hh hA hA1)
    ((S3_ray_density_continuous p a b A h hh hA hA1).intervalIntegrable ψ₁ ψ₂)
