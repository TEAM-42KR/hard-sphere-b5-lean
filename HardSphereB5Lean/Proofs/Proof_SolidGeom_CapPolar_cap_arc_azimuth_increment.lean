import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
import HardSphereB5Lean.Theorems.Thm_SphereGeom_cross_vec_triple
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

private lemma S4_cross_linear_left (p q r : E3) (a b : ℝ) :
    SphereGeom.cross (a • p+b • q) r=a • SphereGeom.cross p r+b • SphereGeom.cross q r := by
  ext k; fin_cases k <;> simp [SphereGeom.cross,crossProduct] <;> ring
private lemma S4_cross_linear_right (p q r : E3) (a b : ℝ) :
    SphereGeom.cross p (a • q+b • r)=a • SphereGeom.cross p q+b • SphereGeom.cross p r := by
  ext k; fin_cases k <;> simp [SphereGeom.cross,crossProduct] <;> ring
private lemma S4_cross_smul_right (p q : E3) (a : ℝ) :
    SphereGeom.cross p (a • q)=a • SphereGeom.cross p q := by
  simpa using S4_cross_linear_right p q q a 0
private lemma S4_cross_sub (p q r : E3) :
    SphereGeom.cross p (q-r)=SphereGeom.cross p q-SphereGeom.cross p r := by
  ext k; fin_cases k <;> simp [SphereGeom.cross,crossProduct] <;> ring
private lemma S4_cross_self (p : E3) : SphereGeom.cross p p=0 := by
  ext k; fin_cases k <;> simp [SphereGeom.cross,crossProduct] <;> ring
private lemma S4_cross_swap (p q : E3) : SphereGeom.cross p q= -SphereGeom.cross q p := by
  ext k; fin_cases k <;> simp [SphereGeom.cross,crossProduct] <;> ring

private lemma S4_exit_hasDerivAt (p a b : E3) (A h ψ : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1)
    (hp : inner ℝ p p=1) (ha : inner ℝ a a=1) (hpa : inner ℝ p a=0)
    (hb : SphereGeom.cross p a=b) :
    HasDerivAt (capExitPoint p a b A h)
      ((exitSin A h ψ/rayRadical A h ψ) •
        SphereGeom.cross (capAxis p a A) (capExitPoint p a b A h ψ)) ψ := by
  let C := exitCos A h ψ
  let S := exitSin A h ψ
  let T := Real.sin ψ
  let V := Real.cos ψ
  let β := capBeta A
  let R := rayRadical A h ψ
  have hr := S3_radius_hasDerivAt A h ψ hh hA hA1
  have hC : HasDerivAt (exitCos A h) (-S*(-β*T*S/R)) ψ := by
    have H := hr.cos
    have heq : (fun s => Real.cos (exitRadius A h s))=exitCos A h :=
      funext (fun s => (S3_radius_trig A h s hh hA hA1).1)
    rw [heq] at H
    rw [(S3_radius_trig A h ψ hh hA hA1).2] at H
    exact H
  have hS : HasDerivAt (exitSin A h) (C*(-β*T*S/R)) ψ := by
    have H := hr.sin
    have heq : (fun s => Real.sin (exitRadius A h s))=exitSin A h :=
      funext (fun s => (S3_radius_trig A h s hh hA hA1).2)
    rw [heq] at H
    rw [(S3_radius_trig A h ψ hh hA hA1).1] at H
    exact H
  have hW := ((hasDerivAt_cos ψ).smul_const a).add ((hasDerivAt_sin ψ).smul_const b)
  have hd := (hC.smul_const p).add (hS.smul hW)
  change HasDerivAt (capExitPoint p a b A h) _ ψ at hd
  apply hd.congr_deriv
  have hpb : SphereGeom.cross p b= -a := by
    rw [← hb,SphereGeom.cross_vec_triple,hp,hpa]; simp
  have hab : SphereGeom.cross a b=p := by
    rw [← hb,SphereGeom.cross_vec_triple,ha,hpa]; simp
  have hap : SphereGeom.cross a p= -b := by rw [S4_cross_swap,hb]
  have hpR : R≠0 := (S3_radical_pos A h ψ hh hA hA1).ne'
  have hR : A*S-β*V*C=R := (S3_CS_exit A h ψ hh hA hA1).2
  have hc : T^2+V^2=1 := Real.sin_sq_add_cos_sq ψ
  have h1 : -S*(-β*T*S/R)=(S/R)*(β*S*T) := by ring
  have h2 : C*(-β*T*S/R)*V+S*(-T)=(S/R)*(-A*S*T) := by
    field_simp [hpR]
    linear_combination S*T*hR
  have h3 : C*(-β*T*S/R)*T+S*V=(S/R)*(A*S*V-β*C) := by
    field_simp [hpR]
    linear_combination -S*V*hR-β*S*C*hc
  calc
    _ = (-S*(-β*T*S/R)) • p+
      (C*(-β*T*S/R)*V+S*(-T)) • a+(C*(-β*T*S/R)*T+S*V) • b := by
      dsimp only [Pi.add_apply]
      module
    _ = _ := by
      rw [h1,h2,h3]
      unfold capAxis capExitPoint capDirection
      simp only [S4_cross_linear_left,S4_cross_linear_right,S4_cross_self,hb,hpb,hab,hap,
        smul_zero,zero_smul,zero_add,add_zero]
      module

private lemma S4_cap_curve_hasDerivAt (e f g : E3) (h t : ℝ)
    (hee : inner ℝ e e=1) (hef : inner ℝ e f=0) (hg : SphereGeom.cross e f=g) :
    HasDerivAt (fun s => h • e+Real.sqrt (1-h^2) • (Real.cos s • f+Real.sin s • g))
      (SphereGeom.cross e (h • e+Real.sqrt (1-h^2) • (Real.cos t • f+Real.sin t • g))) t := by
  have hegc : SphereGeom.cross e g= -f := by
    rw [← hg,SphereGeom.cross_vec_triple,hee,hef]; simp
  have hd := (hasDerivAt_const t (h • e)).add
    ((hasDerivAt_const t (Real.sqrt (1-h^2))).smul
      (((hasDerivAt_cos t).smul_const f).add ((hasDerivAt_sin t).smul_const g)))
  apply hd.congr_deriv
  simp only [zero_smul,zero_add,add_zero,S4_cross_linear_right,S4_cross_self,hg,hegc]
  module

private lemma S4_cap_cross_ne_zero (e f g : E3) (h t : ℝ)
    (hh : 0<h) (hh1 : h<1) (hf : Orthonormal ℝ (fun k : Fin 3 => ![e,f,g] k))
    (hg : SphereGeom.cross e f=g) :
    SphereGeom.cross e (h • e+Real.sqrt (1-h^2) • (Real.cos t • f+Real.sin t • g))≠0 := by
  have H := orthonormal_iff_ite.mp hf
  have hee : inner ℝ e e=1 := by simpa using H 0 0
  have hef : inner ℝ e f=0 := by simpa using H 0 1
  have hff : inner ℝ f f=1 := by simpa using H 1 1
  have hgg : inner ℝ g g=1 := by simpa using H 2 2
  have hfg : inner ℝ f g=0 := by simpa using H 1 2
  have hgf : inner ℝ g f=0 := by simpa using H 2 1
  have hegc : SphereGeom.cross e g= -f := by
    rw [← hg,SphereGeom.cross_vec_triple,hee,hef]; simp
  have hi : inner ℝ
      (SphereGeom.cross e (h • e+Real.sqrt (1-h^2) • (Real.cos t • f+Real.sin t • g)))
      (SphereGeom.cross e (h • e+Real.sqrt (1-h^2) • (Real.cos t • f+Real.sin t • g)))=1-h^2 := by
    simp only [S4_cross_linear_right,S4_cross_self,hg,hegc,smul_zero,zero_add]
    simp only [real_inner_smul_left,real_inner_smul_right,inner_add_left,inner_add_right,
      inner_neg_left,inner_neg_right,hff,hgg,hfg,hgf,mul_one,mul_zero,add_zero,zero_add,neg_zero]
    calc
      _ = Real.sqrt (1-h^2)^2*(Real.cos t^2+Real.sin t^2) := by ring
      _ = _ := by rw [Real.sq_sqrt (by nlinarith),Real.cos_sq_add_sin_sq,mul_one]
  intro hz
  rw [hz] at hi
  simp only [inner_zero_left] at hi
  nlinarith

theorem proof_SolidGeom_CapPolar_cap_arc_azimuth_increment
    (p a b e f g : SphereGeom.E3) (A h L : ℝ) (q : ℝ → ℝ) (O : Set ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1) (hL : 0<L)
    (hpole : Orthonormal ℝ (fun k : Fin 3 => ![p,a,b] k))
    (hb : SphereGeom.cross p a=b) (he : e=SolidGeom.CapPolar.capAxis p a A)
    (hcap : Orthonormal ℝ (fun k : Fin 3 => ![e,f,g] k))
    (hg : SphereGeom.cross e f=g) (hO : IsOpen O) (hI : Set.Icc 0 L ⊆ O)
    (hq : DifferentiableOn ℝ q O)
    (hcurve : Set.EqOn (fun t => SolidGeom.CapPolar.capExitPoint p a b A h (q t))
      (fun t => h • e+Real.sqrt (1-h^2) • (Real.cos t • f+Real.sin t • g)) O) :
    SolidGeom.CapPolar.momentAzimuth A h (q L)-SolidGeom.CapPolar.momentAzimuth A h (q 0)=L  := by
  have HP := orthonormal_iff_ite.mp hpole
  have hp : inner ℝ p p=1 := by simpa using HP 0 0
  have ha : inner ℝ a a=1 := by simpa using HP 1 1
  have hpa : inner ℝ p a=0 := by simpa using HP 0 1
  have HC := orthonormal_iff_ite.mp hcap
  have hee : inner ℝ e e=1 := by simpa using HC 0 0
  have hef : inner ℝ e f=0 := by simpa using HC 0 1
  let U : ℝ → E3 := fun t => capExitPoint p a b A h (q t)
  let V : ℝ → E3 := fun t => h • e+Real.sqrt (1-h^2) • (Real.cos t • f+Real.sin t • g)
  have hφ : ∀ t ∈ Set.uIcc 0 L,
      HasDerivAt (fun s => momentAzimuth A h (q s)) (1 : ℝ) t := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 L := by simpa only [Set.uIcc_of_le hL.le] using ht
    have htO := hI ht'
    have hqd : DifferentiableAt ℝ q t := (hq t htO).differentiableAt (hO.mem_nhds htO)
    have hD := (S4_exit_hasDerivAt p a b A h (q t) hh hA hA1 hp ha hpa hb).scomp t hqd.hasDerivAt
    have hcapD := S4_cap_curve_hasDerivAt e f g h t hee hef hg
    have heq : U =ᶠ[nhds t] V := by
      filter_upwards [hO.mem_nhds htO] with s hs
      exact hcurve hs
    have hpoint : U t=V t := hcurve htO
    have hspeed : (exitSin A h (q t)/rayRadical A h (q t)*deriv q t) •
        SphereGeom.cross e (V t)=SphereGeom.cross e (V t) := by
      have hd1 := hD.deriv
      have hd2 := hcapD.deriv
      have hhD := heq.deriv_eq
      change deriv U t=deriv V t at hhD
      change deriv U t=deriv q t •
        ((exitSin A h (q t)/rayRadical A h (q t)) •
          SphereGeom.cross (capAxis p a A) (U t)) at hd1
      rw [← he,hpoint,smul_smul,mul_comm] at hd1
      rw [hd1,hd2] at hhD
      exact hhD
    have hzero : SphereGeom.cross e (V t)≠0 :=
      S4_cap_cross_ne_zero e f g h t hh (hA.trans_le hA1) hcap hg
    have hmul : exitSin A h (q t)/rayRadical A h (q t)*deriv q t=1 := by
      have hs : (exitSin A h (q t)/rayRadical A h (q t)*deriv q t-1) •
          SphereGeom.cross e (V t)=0 := by rw [sub_smul,one_smul,hspeed,sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hzero)
    have H := (S3_azimuth_hasDerivAt A h (q t) hh hA hA1).comp t hqd.hasDerivAt
    rw [hmul] at H
    exact H
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hφ
    (continuous_const.intervalIntegrable 0 L)
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] using hFTC.symm
