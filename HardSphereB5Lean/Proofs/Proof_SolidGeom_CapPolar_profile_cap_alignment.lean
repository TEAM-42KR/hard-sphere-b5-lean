import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_Profile
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
import HardSphereB5Lean.Theorems.Thm_SphereGeom_cross_vec_triple
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
set_option maxHeartbeats 2400000
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

private def PA_a (E : Fin 3 → E3) (δ : ℝ) : E3 :=
  Real.cos δ • E 0+Real.sin δ • E 1
private def PA_b (E : Fin 3 → E3) (δ : ℝ) : E3 :=
  Real.cos δ • E 1-Real.sin δ • E 0

private lemma PA_rotated_frame (E : Fin 3 → E3) (hE : Orthonormal ℝ E) (δ : ℝ) :
    Orthonormal ℝ (fun k : Fin 3 => ![E 2,PA_a E δ,PA_b E δ] k) := by
  have H := orthonormal_iff_ite.mp hE
  have h00 : inner ℝ (E 0) (E 0)=1 := by simpa using H 0 0
  have h11 : inner ℝ (E 1) (E 1)=1 := by simpa using H 1 1
  have h22 : inner ℝ (E 2) (E 2)=1 := by simpa using H 2 2
  have h01 : inner ℝ (E 0) (E 1)=0 := by simpa using H 0 1
  have h10 : inner ℝ (E 1) (E 0)=0 := by simpa using H 1 0
  have h02 : inner ℝ (E 0) (E 2)=0 := by simpa using H 0 2
  have h20 : inner ℝ (E 2) (E 0)=0 := by simpa using H 2 0
  have h12 : inner ℝ (E 1) (E 2)=0 := by simpa using H 1 2
  have h21 : inner ℝ (E 2) (E 1)=0 := by simpa using H 2 1
  have haa : inner ℝ (PA_a E δ) (PA_a E δ)=1 := by
    unfold PA_a
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      h00,h11,h01,h10,mul_zero,mul_one,zero_add,add_zero]
    nlinarith [Real.cos_sq_add_sin_sq δ]
  have hbb : inner ℝ (PA_b E δ) (PA_b E δ)=1 := by
    unfold PA_b
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
      h00,h11,h01,h10,mul_zero,mul_one,zero_sub,sub_zero]
    nlinarith [Real.cos_sq_add_sin_sq δ]
  have hab : inner ℝ (PA_a E δ) (PA_b E δ)=0 := by
    unfold PA_a PA_b
    simp only [inner_add_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
      h00,h11,h01,h10,mul_zero,mul_one]
    ring
  have hba : inner ℝ (PA_b E δ) (PA_a E δ)=0 := (real_inner_comm _ _).trans hab
  have hpa : inner ℝ (E 2) (PA_a E δ)=0 := by
    simp only [PA_a,inner_add_right,real_inner_smul_right,h20,h21,mul_zero,add_zero]
  have hpb : inner ℝ (E 2) (PA_b E δ)=0 := by
    simp only [PA_b,inner_sub_right,real_inner_smul_right,h20,h21,mul_zero,sub_self]
  have hap : inner ℝ (PA_a E δ) (E 2)=0 := (real_inner_comm _ _).trans hpa
  have hbp : inner ℝ (PA_b E δ) (E 2)=0 := (real_inner_comm _ _).trans hpb
  apply orthonormal_iff_ite.mpr
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first | exact h22 | exact haa | exact hbb | exact hab | exact hba | exact hpa | exact hpb | exact hap | exact hbp

private lemma PA_rotated_orientation (E : Fin 3 → E3) (hE : Orthonormal ℝ E)
    (hor : SphereGeom.cross (E 2) (E 0)=E 1) (δ : ℝ) :
    SphereGeom.cross (E 2) (PA_a E δ)=PA_b E δ := by
  have H := orthonormal_iff_ite.mp hE
  have hp : inner ℝ (E 2) (E 2)=1 := by simpa using H 2 2
  have hpa : inner ℝ (E 2) (E 0)=0 := by simpa using H 2 0
  have hx : SphereGeom.cross (E 2) (E 1)= -(E 0) := by
    rw [← hor,SphereGeom.cross_vec_triple,hp,hpa]
    simp
  unfold PA_a PA_b
  rw [CP_cross_r,hor,hx]
  module

private lemma PA_polar_phase (E : Fin 3 → E3) (ρ φ δ : ℝ) :
    polar E ρ φ=polarRay (E 2) (PA_a E δ) (PA_b E δ) (φ-δ) ρ := by
  have hcos : Real.cos (φ-δ)*Real.cos δ-Real.sin (φ-δ)*Real.sin δ=Real.cos φ := by
    simpa using (Real.cos_add (φ-δ) δ).symm
  have hsin : Real.cos (φ-δ)*Real.sin δ+Real.sin (φ-δ)*Real.cos δ=Real.sin φ := by
    have H := Real.sin_add (φ-δ) δ
    convert H.symm using 1 <;> ring
  unfold polar polarRay PA_a PA_b
  calc
    _ = Real.cos ρ • E 2+
      (Real.sin ρ*(Real.cos (φ-δ)*Real.cos δ-Real.sin (φ-δ)*Real.sin δ)) • E 0+
      (Real.sin ρ*(Real.cos (φ-δ)*Real.sin δ+Real.sin (φ-δ)*Real.cos δ)) • E 1 := by
        rw [hcos,hsin]
        module
    _ = _ := by module

private lemma PA_normal_decompose (E : Fin 3 → E3) (hE : Orthonormal ℝ E)
    (hor : SphereGeom.cross (E 2) (E 0)=E 1) (n : E3) :
    n=(inner ℝ (E 0) n) • E 0+(inner ℝ (E 1) n) • E 1+
      (inner ℝ n (E 2)) • E 2 := by
  have H := orthonormal_iff_ite.mp hE
  have h00 : inner ℝ (E 0) (E 0)=1 := by simpa using H 0 0
  have h11 : inner ℝ (E 1) (E 1)=1 := by simpa using H 1 1
  have h22 : inner ℝ (E 2) (E 2)=1 := by simpa using H 2 2
  have h01 : inner ℝ (E 0) (E 1)=0 := by simpa using H 0 1
  have h02 : inner ℝ (E 0) (E 2)=0 := by simpa using H 0 2
  have h12 : inner ℝ (E 1) (E 2)=0 := by simpa using H 1 2
  have hx : SphereGeom.cross (E 0) (E 1)=E 2 := by
    have h20 : inner ℝ (E 2) (E 0)=0 := by simpa using H 2 0
    rw [← hor,SphereGeom.cross_vec_triple,h00,h20]
    simp
  let z := inner ℝ n (E 2)
  have htan : inner ℝ (n-z • E 2) (SphereGeom.cross (E 0) (E 1))=0 := by
    rw [hx]
    simp only [inner_sub_left,real_inner_smul_left,h22,mul_one,z,sub_self]
  have hd := CP_plane_decompose (E 0) (E 1) (n-z • E 2) h00 h11 h01 htan
  simp only [inner_sub_right,real_inner_smul_right,h02,h12,mul_zero,sub_zero] at hd
  calc
    _ = (n-z • E 2)+z • E 2 := by abel
    _ = _ := by rw [hd]

private lemma PA_normal_coordinates (E : Fin 3 → E3) (hE : Orthonormal ℝ E)
    (hor : SphereGeom.cross (E 2) (E 0)=E 1) (n : E3) (hn : ‖n‖=1) :
    (inner ℝ (E 0) n)^2+(inner ℝ (E 1) n)^2+(inner ℝ n (E 2))^2=1 := by
  have H := orthonormal_iff_ite.mp hE
  let x := inner ℝ (E 0) n
  let y := inner ℝ (E 1) n
  let z := inner ℝ n (E 2)
  have hd : n=x • E 0+y • E 1+z • E 2 := PA_normal_decompose E hE hor n
  have he : inner ℝ (x • E 0+y • E 1+z • E 2) (x • E 0+y • E 1+z • E 2)=x^2+y^2+z^2 := by
    have h00 : inner ℝ (E 0) (E 0)=1 := by simpa using H 0 0
    have h11 : inner ℝ (E 1) (E 1)=1 := by simpa using H 1 1
    have h22 : inner ℝ (E 2) (E 2)=1 := by simpa using H 2 2
    have h01 : inner ℝ (E 0) (E 1)=0 := by simpa using H 0 1
    have h10 : inner ℝ (E 1) (E 0)=0 := by simpa using H 1 0
    have h02 : inner ℝ (E 0) (E 2)=0 := by simpa using H 0 2
    have h20 : inner ℝ (E 2) (E 0)=0 := by simpa using H 2 0
    have h12 : inner ℝ (E 1) (E 2)=0 := by simpa using H 1 2
    have h21 : inner ℝ (E 2) (E 1)=0 := by simpa using H 2 1
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      h00,h11,h22,h01,h10,h02,h20,h12,h21,mul_zero,mul_one,zero_add,add_zero]
    ring
  rw [← hd,real_inner_self_eq_norm_sq,hn] at he
  simpa only [one_pow] using he.symm

private lemma PA_normal_phase (E : Fin 3 → E3) (hE : Orthonormal ℝ E)
    (hor : SphereGeom.cross (E 2) (E 0)=E 1) (n : E3) (hn : ‖n‖=1)
    (hz : 0 < inner ℝ n (E 2)) :
    inner ℝ n (E 2)≤1 ∧ ∃ δ : ℝ,
      n=capAxis (E 2) (PA_a E δ) (inner ℝ n (E 2)) := by
  let x := inner ℝ (E 0) n
  let y := inner ℝ (E 1) n
  let A := inner ℝ n (E 2)
  let β := capBeta A
  have hs : x^2+y^2+A^2=1 := PA_normal_coordinates E hE hor n hn
  have hA1 : A≤1 := by nlinarith [sq_nonneg x,sq_nonneg y]
  have hβ : 0≤β := Real.sqrt_nonneg _
  have hβsq : β^2=1-A^2 := Real.sq_sqrt (by nlinarith [sq_nonneg x,sq_nonneg y])
  refine ⟨hA1,?_⟩
  by_cases hb0 : β=0
  · have hx : x=0 := by rw [hb0] at hβsq; nlinarith [sq_nonneg y]
    have hy : y=0 := by rw [hb0] at hβsq; nlinarith [sq_nonneg x]
    refine ⟨0,?_⟩
    have hd := PA_normal_decompose E hE hor n
    change n=x • E 0+y • E 1+A • E 2 at hd
    rw [hx,hy] at hd
    unfold capAxis
    change n=A • E 2+β • PA_a E 0
    rw [hb0]
    simpa only [zero_smul,zero_add,add_zero] using hd
  · let c : ℂ := ⟨x,y⟩
    have hc : ‖c‖=β := by
      rw [Complex.norm_def]
      have he : Complex.normSq c=β^2 := by
        simp only [Complex.normSq_apply,c]
        nlinarith [hs,hβsq]
      rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg hβ]
    have hc0 : c≠0 := by intro hh; rw [hh,norm_zero] at hc; exact hb0 hc.symm
    have hcos : Real.cos (Complex.arg c)=x/β := by rw [Complex.cos_arg hc0,hc]
    have hsin : Real.sin (Complex.arg c)=y/β := by rw [Complex.sin_arg,hc]
    have hx : β*Real.cos (Complex.arg c)=x := by rw [hcos]; field_simp
    have hy : β*Real.sin (Complex.arg c)=y := by rw [hsin]; field_simp
    refine ⟨Complex.arg c,?_⟩
    have hd := PA_normal_decompose E hE hor n
    change n=x • E 0+y • E 1+A • E 2 at hd
    calc
      n = x • E 0+y • E 1+A • E 2 := hd
      _ = capAxis (E 2) (PA_a E (Complex.arg c)) A := by
        unfold capAxis PA_a
        change x • E 0+y • E 1+A • E 2 = A • E 2+β • (Real.cos (Complex.arg c) • E 0+Real.sin (Complex.arg c) • E 1)
        rw [smul_add,smul_smul,smul_smul,hx,hy]
        abel
private lemma PA_profile_root_matching (P : Profile)
    (hor : SphereGeom.cross (P.e 2) (P.e 0)=P.e 1) (j : Fin 3) (δ : ℝ)
    (hA1 : inner ℝ (P.normal j) (P.e 2)≤1)
    (haxis : P.normal j=capAxis (P.e 2) (PA_a P.e δ) (inner ℝ (P.normal j) (P.e 2)))
    (φ : ℝ) :
    P.rho j φ=exitRadius (inner ℝ (P.normal j) (P.e 2)) (P.height j) (φ-δ) ∧
    polar P.e (P.rho j φ) φ=capExitPoint (P.e 2) (PA_a P.e δ) (PA_b P.e δ)
      (inner ℝ (P.normal j) (P.e 2)) (P.height j) (φ-δ) := by
  let A := inner ℝ (P.normal j) (P.e 2)
  let h := P.height j
  let r := P.rho j φ
  let ψ := φ-δ
  have hf := orthonormal_iff_ite.mp (PA_rotated_frame P.e P.frame δ)
  have hpp : inner ℝ (P.e 2) (P.e 2)=1 := by simpa using hf 0 0
  have haa : inner ℝ (PA_a P.e δ) (PA_a P.e δ)=1 := by simpa using hf 1 1
  have hpa : inner ℝ (P.e 2) (PA_a P.e δ)=0 := by simpa using hf 0 1
  have hap : inner ℝ (PA_a P.e δ) (P.e 2)=0 := by simpa using hf 1 0
  have hpb : inner ℝ (P.e 2) (PA_b P.e δ)=0 := by simpa using hf 0 2
  have hab : inner ℝ (PA_a P.e δ) (PA_b P.e δ)=0 := by simpa using hf 1 2
  have hr := P.rho_range j φ
  have hs : 0<Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2
  have hcap : A*Real.cos r+capBeta A*Real.cos ψ*Real.sin r=h := by
    have H := P.ray_boundary j φ
    rw [PA_polar_phase P.e (P.rho j φ) φ δ,haxis] at H
    have he : inner ℝ (capAxis (P.e 2) (PA_a P.e δ) A)
        (polarRay (P.e 2) (PA_a P.e δ) (PA_b P.e δ) ψ r) =
        A*Real.cos r+capBeta A*Real.cos ψ*Real.sin r := by
      unfold capAxis polarRay
      simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
        hpp,haa,hpa,hap,hpb,hab,mul_zero,mul_one,zero_add,add_zero]
      ring
    rw [he] at H
    exact H
  have H := CP_exit_unique A h ψ (Real.cos r) (Real.sin r)
    (P.height_pos j) (P.pole_inside j) hA1
    (by nlinarith [Real.sin_sq_add_cos_sq r]) hs hcap
  constructor
  · unfold exitRadius
    rw [← H.1,Real.arccos_cos hr.1.le hr.2.le]
  · rw [PA_polar_phase P.e (P.rho j φ) φ δ]
    unfold polarRay capExitPoint capDirection
    change Real.cos r • P.e 2+Real.sin r • (Real.cos ψ • PA_a P.e δ+Real.sin ψ • PA_b P.e δ)=
      exitCos A h ψ • P.e 2+exitSin A h ψ • (Real.cos ψ • PA_a P.e δ+Real.sin ψ • PA_b P.e δ)
    rw [H.1,H.2]

theorem proof_SolidGeom_CapPolar_profile_cap_alignment
    (P : SolidGeom.CapPolar.Profile)
    (hor : SphereGeom.cross (P.e 2) (P.e 0)=P.e 1) (j : Fin 3) :
    ∃ (a b : SphereGeom.E3) (δ : ℝ),
      Orthonormal ℝ (fun k : Fin 3 => ![P.e 2,a,b] k) ∧
      SphereGeom.cross (P.e 2) a=b ∧
      P.normal j=SolidGeom.CapPolar.capAxis (P.e 2) a (inner ℝ (P.normal j) (P.e 2)) ∧
      0 < P.height j ∧ P.height j < inner ℝ (P.normal j) (P.e 2) ∧
      inner ℝ (P.normal j) (P.e 2)≤1 ∧
      a=Real.cos δ • P.e 0+Real.sin δ • P.e 1 ∧
      b=Real.cos δ • P.e 1-Real.sin δ • P.e 0 ∧
      ∀ φ : ℝ,
        P.rho j φ=SolidGeom.CapPolar.exitRadius (inner ℝ (P.normal j) (P.e 2)) (P.height j) (φ-δ) ∧
        SolidGeom.CapPolar.polar P.e (P.rho j φ) φ=
          SolidGeom.CapPolar.capExitPoint (P.e 2) a b (inner ℝ (P.normal j) (P.e 2)) (P.height j) (φ-δ)  := by
  have hz : 0 < inner ℝ (P.normal j) (P.e 2) := (P.height_pos j).trans (P.pole_inside j)
  obtain ⟨hA1,δ,haxis⟩ := PA_normal_phase P.e P.frame hor (P.normal j) (P.normal_unit j) hz
  refine ⟨PA_a P.e δ,PA_b P.e δ,δ,
    PA_rotated_frame P.e P.frame δ,PA_rotated_orientation P.e P.frame hor δ,haxis,
    P.height_pos j,P.pole_inside j,hA1,rfl,rfl,?_⟩
  intro φ
  exact PA_profile_root_matching P hor j δ hA1 haxis φ
