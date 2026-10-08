import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
import HardSphereB5Lean.Theorems.Thm_SphereGeom_cross_vec_triple
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
set_option maxHeartbeats 2000000

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

private def CP_X (A c t : ℝ) := A*Real.cos t+c
private def CP_D (A c t : ℝ) := A*Real.cos t^2+Real.sin t^2+c*Real.cos t
private def CP_N (A c t : ℝ) := (1-A)*Real.sin t*Real.cos t-c*Real.sin t
private def CP_Q (A c t : ℝ) := t+Real.arctan (CP_N A c t/CP_D A c t)
private def CP_rad (A c t : ℝ) := Real.sqrt ((CP_X A c t)^2+Real.sin t^2)

private lemma CP_D_pos (A c t : ℝ) (hc0 : 0≤c) (hc : c<A) (ha1 : A≤1) :
    0<CP_D A c t := by
  have hs := Real.sin_sq_add_cos_sq t
  have hn := mul_nonneg hc0 (show 0≤Real.cos t+1 by linarith [Real.neg_one_le_cos t])
  unfold CP_D
  nlinarith [sq_nonneg (Real.sin t)]
private lemma CP_norm_rotation (A c t : ℝ) :
    CP_D A c t^2+CP_N A c t^2=CP_X A c t^2+Real.sin t^2 := by
  calc
    _ = ((CP_X A c t)^2+Real.sin t^2)*(Real.cos t^2+Real.sin t^2) := by
      unfold CP_D CP_N CP_X
      ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq,mul_one]
private lemma CP_rad_pos (A c t : ℝ) (hc0 : 0≤c) (hc : c<A) (ha1 : A≤1) :
    0<CP_rad A c t := by
  unfold CP_rad
  rw [← CP_norm_rotation]
  apply Real.sqrt_pos.mpr
  nlinarith [sq_pos_of_pos (CP_D_pos A c t hc0 hc ha1),sq_nonneg (CP_N A c t)]
private lemma CP_Q_differentiable (A c : ℝ) (hc0 : 0≤c) (hc : c<A) (ha1 : A≤1) :
    Differentiable ℝ (CP_Q A c) := by
  intro t
  have hquot : DifferentiableAt ℝ (fun s => CP_N A c s/CP_D A c s) t := by
    unfold CP_N CP_D
    fun_prop (disch := exact (CP_D_pos A c t hc0 hc ha1).ne')
  exact differentiableAt_id.add ((Real.hasDerivAt_arctan _).differentiableAt.comp t hquot)
private lemma CP_Q_trig (A c t : ℝ) (hc0 : 0≤c) (hc : c<A) (ha1 : A≤1) :
    Real.cos (CP_Q A c t)=CP_X A c t/CP_rad A c t ∧
    Real.sin (CP_Q A c t)=Real.sin t/CP_rad A c t := by
  have hd := CP_D_pos A c t hc0 hc ha1
  have hr := CP_rad_pos A c t hc0 hc ha1
  have hsqrt : Real.sqrt (1+(CP_N A c t/CP_D A c t)^2)=CP_rad A c t/CP_D A c t := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_pos hr hd).le).mp
    rw [Real.sq_sqrt (by positivity),div_pow]
    have hrad : CP_rad A c t^2=CP_D A c t^2+CP_N A c t^2 := by
      unfold CP_rad
      rw [Real.sq_sqrt (by positivity),CP_norm_rotation]
    rw [div_pow,hrad]
    field_simp [hd.ne']
    <;> ring
  unfold CP_Q
  rw [Real.cos_add,Real.sin_add,Real.cos_arctan,Real.sin_arctan,hsqrt]
  constructor
  · field_simp [hd.ne',hr.ne']
    unfold CP_D CP_N CP_X
    linear_combination (A*Real.cos t+c)*(Real.cos_sq_add_sin_sq t)
  · field_simp [hd.ne',hr.ne']
    unfold CP_D CP_N
    linear_combination Real.sin t*(Real.cos_sq_add_sin_sq t)

private lemma CP_exit_unique (A h ψ C S : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1)
    (hunit : C^2+S^2=1) (hS : 0<S)
    (hcap : A*C+capBeta A*Real.cos ψ*S=h) :
    C=exitCos A h ψ ∧ S=exitSin A h ψ := by
  let B := capBeta A*Real.cos ψ
  let D := A^2+B^2
  let Ce := exitCos A h ψ
  let Se := exitSin A h ψ
  have hAe : A≠0 := (lt_trans hh hA).ne'
  have hD : 0<D := by dsimp [D]; nlinarith [sq_nonneg B]
  have hSe : 0<Se := S3_S_pos A h ψ hh hA hA1
  have hecap : A*Ce+B*Se=h := (S3_CS_exit A h ψ hh hA hA1).1
  have heunit : Ce^2+Se^2=1 := S3_CS_unit A h ψ hh hA hA1
  have quad : ∀ x y : ℝ, x^2+y^2=1 → A*x+B*y=h →
      D*y^2-2*B*h*y+h^2-A^2=0 := by
    intro x y hs he
    have hex : A*x=h-B*y := by linarith
    calc
      _ = (A*x)^2+A^2*y^2-A^2 := by rw [hex]; dsimp [D]; ring
      _ = A^2*(x^2+y^2-1) := by ring
      _ = 0 := by rw [hs]; ring
  have hq := quad C S hunit hcap
  have hqe := quad Ce Se heunit hecap
  have hdif : (S-Se)*(D*(S+Se)-2*B*h)=0 := by linear_combination hq-hqe
  have hseq : S=Se := by
    by_contra hn
    have hx := (mul_eq_zero.mp hdif).resolve_left (sub_ne_zero.mpr hn)
    have hprod : D*S*Se=h^2-A^2 := by linear_combination S*hx-hq
    have hp : 0<D*S*Se := mul_pos (mul_pos hD hS) hSe
    nlinarith
  constructor
  · change C=Ce
    rw [hseq] at hcap
    nlinarith [hcap,hecap]
  · exact hseq

private lemma CP_chart_parameters (A h : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    0<capK h ∧ 0≤h*capBeta A/capK h ∧ h*capBeta A/capK h<A := by
  have hk : 0<capK h := Real.sqrt_pos.mpr (by nlinarith)
  have hb : 0≤capBeta A := Real.sqrt_nonneg _
  have hi : capK h*A>h*capBeta A := by
    have he : (capK h*A)^2-(h*capBeta A)^2=A^2-h^2 := by
      rw [mul_pow,mul_pow,S3_k_sq A h hh hA hA1,S3_beta_sq A h hh hA hA1]
      ring
    have hp := mul_pos hk (lt_trans hh hA)
    nlinarith [mul_nonneg hh.le hb]
  exact ⟨hk,div_nonneg (mul_nonneg hh.le hb) hk.le,
    (div_lt_iff₀ hk).mpr (by nlinarith)⟩

private lemma CP_rad_sq (A c t : ℝ) :
    CP_rad A c t^2=CP_X A c t^2+Real.sin t^2 :=
  Real.sq_sqrt (by positivity)

private lemma CP_canonical_exit_coords (A h t : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    exitCos A h (CP_Q A (h*capBeta A/capK h) t)=h*A-capK h*capBeta A*Real.cos t ∧
    exitSin A h (CP_Q A (h*capBeta A/capK h) t)*Real.cos (CP_Q A (h*capBeta A/capK h) t)=
      h*capBeta A+capK h*A*Real.cos t ∧
    exitSin A h (CP_Q A (h*capBeta A/capK h) t)*Real.sin (CP_Q A (h*capBeta A/capK h) t)=
      capK h*Real.sin t := by
  let β := capBeta A
  let k := capK h
  let c := h*β/k
  let q := CP_Q A c t
  let r := CP_rad A c t
  have H := CP_chart_parameters A h hh hA hA1
  have hp : 0<r := CP_rad_pos A c t H.2.1 H.2.2 hA1
  have hk : k≠0 := H.1.ne'
  have hc : k*c=h*β := by dsimp [c]; field_simp
  have htr := CP_Q_trig A c t H.2.1 H.2.2 hA1
  have hxy : k*r*Real.cos q=h*β+k*A*Real.cos t := by
    have hx : Real.cos q*r=CP_X A c t := (eq_div_iff hp.ne').mp htr.1
    calc
      _ = k*(Real.cos q*r) := by ring
      _ = k*CP_X A c t := by rw [hx]
      _ = _ := by unfold CP_X; linear_combination hc
  have hyy : k*r*Real.sin q=k*Real.sin t := by
    have hy : Real.sin q*r=Real.sin t := (eq_div_iff hp.ne').mp htr.2
    calc
      _ = k*(Real.sin q*r) := by ring
      _ = _ := by rw [hy]
  have hunit : (h*A-k*β*Real.cos t)^2+(k*r)^2=1 := by
    rw [mul_pow,CP_rad_sq]
    have hz : (k*CP_X A c t)^2=(h*β+k*A*Real.cos t)^2 := by
      have hx : k*CP_X A c t=h*β+k*A*Real.cos t := by unfold CP_X; nlinarith [hc]
      rw [hx]
    have hrw : k^2*(CP_X A c t^2+Real.sin t^2)=
        (h*β+k*A*Real.cos t)^2+(k*Real.sin t)^2 := by rw [← hz]; ring
    rw [hrw]
    calc
      _ = h^2*(A^2+β^2)+k^2*Real.cos t^2*(A^2+β^2)+k^2*Real.sin t^2 := by ring
      _ = 1 := by
        have hAB : A^2+β^2=1 := by dsimp [β]; nlinarith [S3_beta_sq A h hh hA hA1]
        rw [hAB]
        have htrig := Real.cos_sq_add_sin_sq t
        have hk2 := S3_k_sq A h hh hA hA1
        change h^2*1+k^2*Real.cos t^2*1+k^2*Real.sin t^2=1
        nlinarith [congrArg (fun z : ℝ => k^2*z) htrig]
  have hcap : A*(h*A-k*β*Real.cos t)+β*Real.cos q*(k*r)=h := by
    have he : β*Real.cos q*(k*r)=β*(h*β+k*A*Real.cos t) := by linear_combination β*hxy
    rw [he]
    have hAB : A^2+β^2=1 := by dsimp [β]; nlinarith [S3_beta_sq A h hh hA hA1]
    calc
      _ = h*(A^2+β^2) := by ring
      _ = h := by rw [hAB,mul_one]
  have he := CP_exit_unique A h q (h*A-k*β*Real.cos t) (k*r) hh hA hA1 hunit
    (mul_pos H.1 hp) hcap
  exact ⟨he.1.symm,by rw [← he.2]; exact hxy,by rw [← he.2]; exact hyy⟩

private lemma CP_chart_point (p a b : E3) (A h t : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    capExitPoint p a b A h (CP_Q A (h*capBeta A/capK h) t) =
      h • (A • p+capBeta A • a)+
        capK h • (Real.cos t • (A • a-capBeta A • p)+Real.sin t • b) := by
  have H := CP_canonical_exit_coords A h t hh hA hA1
  calc
    _ = exitCos A h (CP_Q A (h*capBeta A/capK h) t) • p+
      (exitSin A h (CP_Q A (h*capBeta A/capK h) t)*Real.cos (CP_Q A (h*capBeta A/capK h) t)) • a+
      (exitSin A h (CP_Q A (h*capBeta A/capK h) t)*Real.sin (CP_Q A (h*capBeta A/capK h) t)) • b := by
      unfold capExitPoint capDirection
      module
    _ = _ := by rw [H.1,H.2.1,H.2.2]; module

private lemma CP_cross_l (v w u : E3) (A B : ℝ) :
    SphereGeom.cross (A • v+B • w) u=A • SphereGeom.cross v u+B • SphereGeom.cross w u := by
  ext k; fin_cases k <;> simp [SphereGeom.cross,crossProduct] <;> ring
private lemma CP_cross_r (v w u : E3) (A B : ℝ) :
    SphereGeom.cross v (A • w+B • u)=A • SphereGeom.cross v w+B • SphereGeom.cross v u := by
  ext k; fin_cases k <;> simp [SphereGeom.cross,crossProduct] <;> ring
private lemma CP_cross_self (v : E3) : SphereGeom.cross v v=0 := by
  ext k; fin_cases k <;> simp [SphereGeom.cross,crossProduct] <;> ring
private lemma CP_cross_swap (v w : E3) : SphereGeom.cross v w= -SphereGeom.cross w v := by
  ext k; fin_cases k <;> simp [SphereGeom.cross,crossProduct] <;> ring
private lemma CP_plane_decompose (u v w : E3)
    (hu : inner ℝ u u=1) (hv : inner ℝ v v=1) (huv : inner ℝ u v=0)
    (hwn : inner ℝ w (SphereGeom.cross u v)=0) :
    w=(inner ℝ u w) • u+(inner ℝ v w) • v := by
  have hi : (inner ℝ u u*inner ℝ v v-inner ℝ u v^2) • w =
      (inner ℝ w (SphereGeom.cross u v)) • SphereGeom.cross u v+
      (inner ℝ v v*inner ℝ u w-inner ℝ u v*inner ℝ v w) • u+
      (inner ℝ u u*inner ℝ v w-inner ℝ u v*inner ℝ u w) • v := by
    ext k
    fin_cases k <;> simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,
      EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ] <;> ring
  simpa only [hu,hv,huv,hwn,one_mul,mul_one,zero_mul,
    zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,zero_smul,zero_add,one_smul] using hi

private lemma CP_phase_exists (u v f : E3)
    (hu : inner ℝ u u=1) (hv : inner ℝ v v=1) (huv : inner ℝ u v=0)
    (hf : inner ℝ f f=1) (hfn : inner ℝ f (SphereGeom.cross u v)=0) :
    ∃ θ : ℝ, f=Real.cos θ • u+Real.sin θ • v := by
  let x := inner ℝ u f
  let y := inner ℝ v f
  have hd : f=x • u+y • v := CP_plane_decompose u v f hu hv huv hfn
  have hsq : x^2+y^2=1 := by
    have he : inner ℝ (x • u+y • v) (x • u+y • v)=x^2+y^2 := by
      simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
        hu,hv,huv,show inner ℝ v u=0 from (real_inner_comm u v).trans huv,
        mul_zero,mul_one,zero_add,add_zero]
      ring
    rw [← hd,hf] at he
    exact he.symm
  let z : ℂ := ⟨x,y⟩
  have hnorm : ‖z‖=1 := by
    rw [Complex.norm_def]
    have he : Complex.normSq z=x^2+y^2 := by simp [Complex.normSq_apply,z,pow_two]
    rw [he,hsq]
    norm_num
  have hz : z≠0 := by intro hz; rw [hz,norm_zero] at hnorm; norm_num at hnorm
  refine ⟨Complex.arg z,?_⟩
  have hc : Real.cos (Complex.arg z)=x := by rw [Complex.cos_arg hz,hnorm]; simp [z]
  have hs : Real.sin (Complex.arg z)=y := by rw [Complex.sin_arg,hnorm]; simp [z]
  rw [hc,hs]
  exact hd

private lemma CP_Q_hasDerivAt (A c t : ℝ) (hc0 : 0≤c) (hc : c<A) (ha1 : A≤1) :
    HasDerivAt (CP_Q A c) ((A+c*Real.cos t)/(CP_D A c t^2+CP_N A c t^2)) t := by
  let dn := (1-A)*(Real.cos t^2-Real.sin t^2)-c*Real.cos t
  let dd := 2*(1-A)*Real.sin t*Real.cos t-c*Real.sin t
  have hN : HasDerivAt (CP_N A c) dn t := by
    have h := (((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).const_mul (1-A)).sub
      ((Real.hasDerivAt_sin t).const_mul c)
    have hr : HasDerivAt (fun s : ℝ => (1-A)*(Real.sin s*Real.cos s)-c*Real.sin s)
        ((1-A)*(Real.cos t*Real.cos t+Real.sin t*(-Real.sin t))-c*Real.cos t) t := h
    have hf : (fun s : ℝ => (1-A)*(Real.sin s*Real.cos s)-c*Real.sin s)=CP_N A c := by
      funext s
      dsimp [CP_N]
      ring
    rw [hf] at hr
    have hv : (1-A)*(Real.cos t*Real.cos t+Real.sin t*(-Real.sin t))-c*Real.cos t=dn := by
      dsimp [dn]
      ring
    rwa [hv] at hr
  have hD : HasDerivAt (CP_D A c) dd t := by
    have h := ((((Real.hasDerivAt_cos t).pow 2).const_mul A).add
      ((Real.hasDerivAt_sin t).pow 2)).add ((Real.hasDerivAt_cos t).const_mul c)
    change HasDerivAt (CP_D A c)
      ((A*(2*Real.cos t^(2-1)*(-Real.sin t))+2*Real.sin t^(2-1)*Real.cos t)+c*(-Real.sin t)) t at h
    have hv : (A*(2*Real.cos t^(2-1)*(-Real.sin t))+2*Real.sin t^(2-1)*Real.cos t)+c*(-Real.sin t)=dd := by
      simp only [show (2-1:ℕ)=1 from rfl,pow_one]
      dsimp [dd]
      ring
    rwa [hv] at h
  have hdz : CP_D A c t ≠ 0 := (CP_D_pos A c t hc0 hc ha1).ne'
  have hsum : 0 < CP_D A c t^2+CP_N A c t^2 := by
    nlinarith [sq_pos_of_pos (CP_D_pos A c t hc0 hc ha1),sq_nonneg (CP_N A c t)]
  have hquot := hN.div hD hdz
  have hraw := (hasDerivAt_id t).add ((Real.hasDerivAt_arctan (CP_N A c t/CP_D A c t)).comp t hquot)
  have hdiv : 1+(CP_N A c t/CP_D A c t)^2 =
      (CP_D A c t^2+CP_N A c t^2)/(CP_D A c t)^2 := by
    field_simp [hdz] <;> ring
  have hpoly : CP_D A c t^2+CP_N A c t^2+dn*CP_D A c t-CP_N A c t*dd = A+c*Real.cos t := by
    dsimp [CP_D,CP_N,dn,dd]
    linear_combination (A*((Real.cos t)^2+(Real.sin t)^2+1)+c*Real.cos t)*
      (Real.cos_sq_add_sin_sq t)
  change HasDerivAt (CP_Q A c)
    (1+(1/(1+(CP_N A c t/CP_D A c t)^2))*
      ((dn*CP_D A c t-CP_N A c t*dd)/(CP_D A c t)^2)) t at hraw
  have hpiece : (1/(1+(CP_N A c t/CP_D A c t)^2))*
      ((dn*CP_D A c t-CP_N A c t*dd)/(CP_D A c t)^2) =
      (dn*CP_D A c t-CP_N A c t*dd)/(CP_D A c t^2+CP_N A c t^2) := by
    rw [hdiv]
    field_simp [hdz,hsum.ne'] <;> ring
  have hder : (A+c*Real.cos t)/(CP_D A c t^2+CP_N A c t^2) =
      1+(1/(1+(CP_N A c t/CP_D A c t)^2))*
        ((dn*CP_D A c t-CP_N A c t*dd)/(CP_D A c t)^2) := by
    rw [hpiece]
    calc
      _ = ((CP_D A c t^2+CP_N A c t^2)+(dn*CP_D A c t-CP_N A c t*dd))/
          (CP_D A c t^2+CP_N A c t^2) := by congr 1; linarith only [hpoly]
      _ = _ := by rw [add_div,div_self hsum.ne']
  rw [← hder] at hraw
  exact hraw

private lemma CP_Q_strictMono (A c : ℝ) (hc0 : 0≤c) (hc : c<A) (ha1 : A≤1) :
    StrictMono (CP_Q A c) := by
  have hm : StrictMonoOn (CP_Q A c) Set.univ := by
    apply strictMonoOn_of_deriv_pos convex_univ (CP_Q_differentiable A c hc0 hc ha1).continuous.continuousOn
    intro t ht
    rw [(CP_Q_hasDerivAt A c t hc0 hc ha1).deriv]
    apply div_pos
    · have hn := mul_nonneg hc0 (show 0≤Real.cos t+1 by linarith [Real.neg_one_le_cos t])
      nlinarith
    · nlinarith [sq_pos_of_pos (CP_D_pos A c t hc0 hc ha1),sq_nonneg (CP_N A c t)]
  intro a b hab
  exact hm (Set.mem_univ a) (Set.mem_univ b) hab

private lemma CP_Q_period (A c t : ℝ) : CP_Q A c (t+2*Real.pi)=CP_Q A c t+2*Real.pi := by
  simp only [CP_Q,CP_N,CP_D,Real.cos_add_two_pi,Real.sin_add_two_pi]
  ring

theorem proof_SolidGeom_CapPolar_cap_circle_polar_chart_ordered
    (p a b e f g : SphereGeom.E3) (A h : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1)
    (hpole : Orthonormal ℝ (fun k : Fin 3 => ![p,a,b] k))
    (hb : SphereGeom.cross p a=b) (he : e=SolidGeom.CapPolar.capAxis p a A)
    (hcap : Orthonormal ℝ (fun k : Fin 3 => ![e,f,g] k))
    (hg : SphereGeom.cross e f=g) :
    ∃ q : ℝ → ℝ, Differentiable ℝ q ∧ StrictMono q ∧
      (∀ t, q (t+2*Real.pi)=q t+2*Real.pi) ∧ ∀ t,
      SolidGeom.CapPolar.capExitPoint p a b A h (q t)=
        h • e+Real.sqrt (1-h^2) • (Real.cos t • f+Real.sin t • g)  := by
  have HP := orthonormal_iff_ite.mp hpole
  have hp : inner ℝ p p=1 := by simpa using HP 0 0
  have ha : inner ℝ a a=1 := by simpa using HP 1 1
  have hbunit : inner ℝ b b=1 := by simpa using HP 2 2
  have hpa : inner ℝ p a=0 := by simpa using HP 0 1
  have hap : inner ℝ a p=0 := by simpa using HP 1 0
  have habzero : inner ℝ a b=0 := by simpa using HP 1 2
  have hpbzero : inner ℝ p b=0 := by simpa using HP 0 2
  have HC := orthonormal_iff_ite.mp hcap
  have hff : inner ℝ f f=1 := by simpa using HC 1 1
  have hfe : inner ℝ f e=0 := by simpa using HC 1 0
  let β := capBeta A
  let s : E3 := A • a+(-β) • p
  have hAB : A^2+β^2=1 := by dsimp [β]; nlinarith [S3_beta_sq A h hh hA hA1]
  have hpb : SphereGeom.cross p b= -a := by
    rw [← hb,SphereGeom.cross_vec_triple,hp,hpa]
    simp
  have hab : SphereGeom.cross a b=p := by
    rw [← hb,SphereGeom.cross_vec_triple,ha,hpa]
    simp
  have hba : SphereGeom.cross a p= -b := by rw [CP_cross_swap,hb]
  have hss : inner ℝ s s=1 := by
    dsimp [s]
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      hp,ha,hpa,hap,mul_one,mul_zero,add_zero,zero_add]
    nlinarith [hAB]
  have hsb : inner ℝ s b=0 := by
    simp only [s,inner_add_left,real_inner_smul_left,habzero,hpbzero,mul_zero,add_zero]
  have hsn : SphereGeom.cross s b=e := by
    dsimp [s]
    rw [CP_cross_l,hab,hpb,he]
    unfold capAxis
    module
  have hes : SphereGeom.cross e s=b := by
    rw [he]
    unfold capAxis
    dsimp [s]
    rw [CP_cross_r,CP_cross_l,CP_cross_l,CP_cross_self,CP_cross_self,hb,hba]
    calc
      _ = (A^2+β^2) • b := by module
      _ = b := by rw [hAB,one_smul]
  have heb : SphereGeom.cross e b= -s := by
    rw [he]
    unfold capAxis
    rw [CP_cross_l,hpb,hab]
    dsimp [s]
    module
  have hfn : inner ℝ f (SphereGeom.cross s b)=0 := by rw [hsn]; exact hfe
  obtain ⟨θ,hphase⟩ := CP_phase_exists s b f hss hbunit hsb hff hfn
  have hgphase : g=(-Real.sin θ) • s+Real.cos θ • b := by
    rw [← hg,hphase,CP_cross_r,hes,heb]
    module
  let c := h*β/capK h
  let q := fun t => CP_Q A c (t+θ)
  have H := CP_chart_parameters A h hh hA hA1
  refine ⟨q,?_,?_,?_,?_⟩
  · exact (CP_Q_differentiable A c H.2.1 H.2.2 hA1).comp (differentiable_id.add_const θ)
  · intro a b hab
    exact CP_Q_strictMono A c H.2.1 H.2.2 hA1 (by linarith : a+θ<b+θ)
  · intro t
    dsimp only [q]
    rw [show t+2*Real.pi+θ=(t+θ)+2*Real.pi by ring,CP_Q_period]
  · intro t
    dsimp only [q,c,β]
    rw [CP_chart_point p a b A h (t+θ) hh hA hA1]
    calc
      _ = h • e+capK h • (Real.cos (t+θ) • s+Real.sin (t+θ) • b) := by
        rw [he]
        unfold capAxis
        dsimp [s,β]
        module
      _ = _ := by
        rw [hphase,hgphase,Real.cos_add,Real.sin_add]
        unfold capK
        module
