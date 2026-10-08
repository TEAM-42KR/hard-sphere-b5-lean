import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_tailAngle
import HardSphereB5Lean.Theorems.Thm_SphereGeom_cross_vec_triple
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
open scoped RealInnerProductSpace
set_option maxHeartbeats 1800000
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

private lemma A4_cross_smul_left (p q : E3) (a : ℝ) :
    SphereGeom.cross (a • p) q=a • SphereGeom.cross p q := by
  simpa using S4_cross_linear_left p p q a 0
private lemma A4_cross_sub_left (p q r : E3) :
    SphereGeom.cross (p-q) r=SphereGeom.cross p r-SphereGeom.cross q r := by
  ext k; fin_cases k <;> simp [SphereGeom.cross,crossProduct] <;> ring
private lemma A4_cross_orthogonal_left (p a : E3) : inner ℝ p (SphereGeom.cross p a)=0 := by
  simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,Fin.sum_univ_succ]
  ring
private lemma A4_cross_orthogonal_right (p a : E3) : inner ℝ a (SphereGeom.cross p a)=0 := by
  simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,Fin.sum_univ_succ]
  ring
private lemma A4_cross_norm (p a : E3) :
    inner ℝ (SphereGeom.cross p a) (SphereGeom.cross p a)=
      inner ℝ p p*inner ℝ a a-(inner ℝ p a)^2 := by
  simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  ring

private lemma A4_asin_turn (x y : ℝ) (hx : |x|<1) (hy : |y|<1) :
    Complex.arg ⟨Real.sqrt (1-x^2)*Real.sqrt (1-y^2)+x*y,
      Real.sqrt (1-x^2)*y-x*Real.sqrt (1-y^2)⟩=Real.arcsin y-Real.arcsin x := by
  have hθ : Real.arcsin y-Real.arcsin x ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.arcsin_lt_pi_div_two.mpr (abs_lt.mp hx).2,
      Real.neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp hx).1,
      Real.arcsin_lt_pi_div_two.mpr (abs_lt.mp hy).2,
      Real.neg_pi_div_two_lt_arcsin.mpr (abs_lt.mp hy).1]
  have he : (⟨Real.sqrt (1-x^2)*Real.sqrt (1-y^2)+x*y,
      Real.sqrt (1-x^2)*y-x*Real.sqrt (1-y^2)⟩ : ℂ)=
      Real.cos (Real.arcsin y-Real.arcsin x)+Real.sin (Real.arcsin y-Real.arcsin x)*Complex.I := by
    apply Complex.ext <;> simp [Real.cos_sub,Real.sin_sub,Real.cos_arcsin,
      Real.sin_arcsin (abs_lt.mp hx).1.le (abs_lt.mp hx).2.le,
      Real.sin_arcsin (abs_lt.mp hy).1.le (abs_lt.mp hy).2.le] <;> ring
  rw [he]
  simpa using Complex.arg_cos_add_sin_mul_I hθ

private lemma A4_tangent_frame (p a b : E3) (A h ψ : ℝ)
    (hp : inner ℝ p p=1) (ha : inner ℝ a a=1) (hpa : inner ℝ p a=0)
    (hb : SphereGeom.cross p a=b) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    inner ℝ (capRadialBasis p a b A h ψ) (capRadialBasis p a b A h ψ)=1 ∧
    inner ℝ (capAzimuthBasis a b ψ) (capAzimuthBasis a b ψ)=1 ∧
    inner ℝ (capRadialBasis p a b A h ψ) (capAzimuthBasis a b ψ)=0 ∧
    SphereGeom.cross (capRadialBasis p a b A h ψ) (capAzimuthBasis a b ψ)=capExitPoint p a b A h ψ ∧
    exitSin A h ψ • capRadialBasis p a b A h ψ=
      exitCos A h ψ • capExitPoint p a b A h ψ-p ∧
    exitSin A h ψ • capAzimuthBasis a b ψ=SphereGeom.cross p (capExitPoint p a b A h ψ) ∧
    SphereGeom.cross (capAxis p a A) (capExitPoint p a b A h ψ)=
      -(capBeta A*Real.sin ψ) • capRadialBasis p a b A h ψ+
      rayRadical A h ψ • capAzimuthBasis a b ψ ∧
    inner ℝ (capExitPoint p a b A h ψ) (capExitPoint p a b A h ψ)=1 := by
  have hpb : inner ℝ p b=0 := hb ▸ A4_cross_orthogonal_left p a
  have hab : inner ℝ a b=0 := hb ▸ A4_cross_orthogonal_right p a
  have hbb : inner ℝ b b=1 := by rw [←hb,A4_cross_norm,hp,ha,hpa]; norm_num
  have hbp : inner ℝ b p=0 := (real_inner_comm p b).trans hpb
  have hba : inner ℝ b a=0 := (real_inner_comm a b).trans hab
  have hap : inner ℝ a p=0 := (real_inner_comm p a).trans hpa
  have hpcb : SphereGeom.cross p b= -a := by rw [←hb,SphereGeom.cross_vec_triple,hp,hpa]; simp
  have hacb : SphereGeom.cross a b=p := by rw [←hb,SphereGeom.cross_vec_triple,ha,hpa]; simp
  have hacp : SphereGeom.cross a p= -b := by rw [S4_cross_swap,hb]
  have hbcp : SphereGeom.cross b p=a := by rw [S4_cross_swap,hpcb,neg_neg]
  have hbca : SphereGeom.cross b a= -p := by rw [S4_cross_swap,hacb]
  have hunit := S3_CS_unit A h ψ hh hA hA1
  have hroot := S3_CS_exit A h ψ hh hA hA1
  have ht := Real.sin_sq_add_cos_sq ψ
  have hrr : inner ℝ (capRadialBasis p a b A h ψ) (capRadialBasis p a b A h ψ)=1 := by
    unfold capRadialBasis capDirection
    simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,hp,ha,hbb,hpa,hap,hpb,hbp,hab,hba]
    nlinarith [congrArg (fun t : ℝ => (exitCos A h ψ)^2*t) ht]
  have hss : inner ℝ (capAzimuthBasis a b ψ) (capAzimuthBasis a b ψ)=1 := by
    unfold capAzimuthBasis
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hbb,ha,hab,hba]
    nlinarith [ht]
  have hrs : inner ℝ (capRadialBasis p a b A h ψ) (capAzimuthBasis a b ψ)=0 := by
    unfold capRadialBasis capDirection capAzimuthBasis
    simp only [inner_sub_left,inner_sub_right,inner_add_left,real_inner_smul_left,real_inner_smul_right,
      ha,hbb,hpa,hpb,hab,hba]
    ring
  refine ⟨hrr,hss,hrs,?_,?_,?_,?_,?_⟩
  · simp only [capRadialBasis,capDirection,capAzimuthBasis,capExitPoint]
    simp only [A4_cross_sub_left,S4_cross_sub,S4_cross_linear_left,S4_cross_linear_right,
      A4_cross_smul_left,S4_cross_smul_right,S4_cross_self,hb,hpcb,hacb,hacp,hbca,hbcp]
    ext k
    simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,PiLp.neg_apply,PiLp.zero_apply,smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => exitCos A h ψ*p k*t) ht,
      congrArg (fun t : ℝ => exitSin A h ψ*a k*t) ht,
      congrArg (fun t : ℝ => exitSin A h ψ*b k*t) ht]
  · simp only [capRadialBasis,capDirection,capExitPoint]
    ext k
    simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => p k*t) hunit]
  · simp only [capExitPoint,capDirection,capAzimuthBasis]
    simp only [S4_cross_linear_right,S4_cross_smul_right,S4_cross_self,hb,hpcb]
    module
  · simp only [capAxis,capExitPoint,capDirection,capRadialBasis,capAzimuthBasis]
    simp only [S4_cross_linear_left,S4_cross_linear_right,S4_cross_smul_right,S4_cross_self,hb,hpcb,hacb,hacp]
    ext k
    simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,PiLp.neg_apply,PiLp.zero_apply,smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => a k*Real.sin ψ*t) hroot.2,
      congrArg (fun t : ℝ => b k*Real.cos ψ*t) hroot.2,
      congrArg (fun t : ℝ => b k*capBeta A*exitCos A h ψ*t) ht]
  · unfold capExitPoint capDirection
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      hp,ha,hbb,hpa,hap,hpb,hbp,hab,hba]
    nlinarith [congrArg (fun t : ℝ => (exitSin A h ψ)^2*t) ht]

private lemma A4_tail_trig (A h ψ : ℝ) (hh : 0<h) (hA : h<A) (hA1 : A≤1) :
    0<capK h ∧ |capBeta A*Real.sin ψ/capK h|<1 ∧
      Real.sqrt (1-(capBeta A*Real.sin ψ/capK h)^2)=rayRadical A h ψ/capK h := by
  have hk : 0<capK h := Real.sqrt_pos.mpr (by nlinarith)
  have hr : 0<rayRadical A h ψ := S3_radical_pos A h ψ hh hA hA1
  have he : rayRadical A h ψ^2+(capBeta A*Real.sin ψ)^2=capK h^2 := by
    rw [S3_radical_sq A h ψ hh hA hA1,S3_k_sq A h hh hA hA1]
    unfold rayDenom
    ring
  have hl : -capK h<capBeta A*Real.sin ψ ∧ capBeta A*Real.sin ψ<capK h := by
    constructor <;> nlinarith [sq_pos_of_pos hr]
  have hab : |capBeta A*Real.sin ψ/capK h|<1 := by
    rw [abs_lt]
    constructor
    · rw [lt_div_iff₀ hk]; linarith [hl.1]
    · rw [div_lt_iff₀ hk]; simpa only [one_mul] using hl.2
  refine ⟨hk,hab,?_⟩
  have hsq : 1-(capBeta A*Real.sin ψ/capK h)^2=(rayRadical A h ψ/capK h)^2 := by
    field_simp [hk.ne']
    nlinarith [he]
  rw [hsq,Real.sqrt_sq_eq_abs,abs_of_pos (div_pos hr hk)]
theorem proof_SolidGeom_CapPolar_cap_corner_tail_angle (p a₁ b₁ a₂ b₂ : SphereGeom.E3)
    (A₁ h₁ ψ₁ A₂ h₂ ψ₂ : ℝ)
    (hp : inner ℝ p p=1)
    (ha₁ : inner ℝ a₁ a₁=1) (hpa₁ : inner ℝ p a₁=0) (hb₁ : SphereGeom.cross p a₁=b₁)
    (ha₂ : inner ℝ a₂ a₂=1) (hpa₂ : inner ℝ p a₂=0) (hb₂ : SphereGeom.cross p a₂=b₂)
    (hh₁ : 0<h₁) (hA₁ : h₁<A₁) (hA₁1 : A₁≤1)
    (hh₂ : 0<h₂) (hA₂ : h₂<A₂) (hA₂1 : A₂≤1)
    (hu : SolidGeom.CapPolar.capExitPoint p a₁ b₁ A₁ h₁ ψ₁ =
      SolidGeom.CapPolar.capExitPoint p a₂ b₂ A₂ h₂ ψ₂) :
    SolidGeom.CapPolar.capCorner (SolidGeom.CapPolar.capExitPoint p a₁ b₁ A₁ h₁ ψ₁)
      (SolidGeom.CapPolar.capAxis p a₁ A₁) (SolidGeom.CapPolar.capAxis p a₂ A₂) =
      SolidGeom.CapPolar.tailAngle A₂ h₂ ψ₂-SolidGeom.CapPolar.tailAngle A₁ h₁ ψ₁  := by
  rcases A4_tangent_frame p a₁ b₁ A₁ h₁ ψ₁ hp ha₁ hpa₁ hb₁ hh₁ hA₁ hA₁1 with
    ⟨hrr₁,hss₁,hrs₁,hcross₁,hrad₁,haz₁,htan₁,hu₁⟩
  rcases A4_tangent_frame p a₂ b₂ A₂ h₂ ψ₂ hp ha₂ hpa₂ hb₂ hh₂ hA₂ hA₂1 with
    ⟨hrr₂,hss₂,hrs₂,hcross₂,hrad₂,haz₂,htan₂,hu₂⟩
  have hpb₁ : inner ℝ p b₁=0 := hb₁ ▸ A4_cross_orthogonal_left p a₁
  have hpb₂ : inner ℝ p b₂=0 := hb₂ ▸ A4_cross_orthogonal_left p a₂
  have hinner₁ : inner ℝ p (capExitPoint p a₁ b₁ A₁ h₁ ψ₁)=exitCos A₁ h₁ ψ₁ := by
    simp only [capExitPoint,capDirection,inner_add_right,real_inner_smul_right,hp,hpa₁,hpb₁]
    ring
  have hinner₂ : inner ℝ p (capExitPoint p a₂ b₂ A₂ h₂ ψ₂)=exitCos A₂ h₂ ψ₂ := by
    simp only [capExitPoint,capDirection,inner_add_right,real_inner_smul_right,hp,hpa₂,hpb₂]
    ring
  have hC : exitCos A₁ h₁ ψ₁=exitCos A₂ h₂ ψ₂ := by rw [←hinner₁,hu,hinner₂]
  have hS : exitSin A₁ h₁ ψ₁=exitSin A₂ h₂ ψ₂ := by
    have hunit₁ := S3_CS_unit A₁ h₁ ψ₁ hh₁ hA₁ hA₁1
    rw [hC] at hunit₁
    have hsq : (exitSin A₁ h₁ ψ₁)^2=(exitSin A₂ h₂ ψ₂)^2 := by
      linarith [hunit₁,S3_CS_unit A₂ h₂ ψ₂ hh₂ hA₂ hA₂1]
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos (S3_S_pos A₁ h₁ ψ₁ hh₁ hA₁ hA₁1),
      abs_of_pos (S3_S_pos A₂ h₂ ψ₂ hh₂ hA₂ hA₂1)] using congrArg Real.sqrt hsq
  have hrad : capRadialBasis p a₁ b₁ A₁ h₁ ψ₁=capRadialBasis p a₂ b₂ A₂ h₂ ψ₂ := by
    rw [hS,hC,hu] at hrad₁
    have he := hrad₁.trans hrad₂.symm
    ext k
    have hk := congrArg (fun v : E3 => v k) he
    simp only [PiLp.smul_apply,smul_eq_mul] at hk
    exact mul_left_cancel₀ (S3_S_pos A₂ h₂ ψ₂ hh₂ hA₂ hA₂1).ne' hk
  have haz : capAzimuthBasis a₁ b₁ ψ₁=capAzimuthBasis a₂ b₂ ψ₂ := by
    rw [hS,hu] at haz₁
    have he := haz₁.trans haz₂.symm
    ext k
    have hk := congrArg (fun v : E3 => v k) he
    simp only [PiLp.smul_apply,smul_eq_mul] at hk
    exact mul_left_cancel₀ (S3_S_pos A₂ h₂ ψ₂ hh₂ hA₂ hA₂1).ne' hk
  have htan₂' : SphereGeom.cross (capAxis p a₂ A₂) (capExitPoint p a₁ b₁ A₁ h₁ ψ₁)=
      -(capBeta A₂*Real.sin ψ₂) • capRadialBasis p a₁ b₁ A₁ h₁ ψ₁+
      rayRadical A₂ h₂ ψ₂ • capAzimuthBasis a₁ b₁ ψ₁ := by
    rw [hu,htan₂,←hrad,←haz]
  have hsr₁ : inner ℝ (capAzimuthBasis a₁ b₁ ψ₁) (capRadialBasis p a₁ b₁ A₁ h₁ ψ₁)=0 :=
    (real_inner_comm (capRadialBasis p a₁ b₁ A₁ h₁ ψ₁) (capAzimuthBasis a₁ b₁ ψ₁)).trans hrs₁
  have hswap : SphereGeom.cross (capAzimuthBasis a₁ b₁ ψ₁) (capRadialBasis p a₁ b₁ A₁ h₁ ψ₁)=
      -capExitPoint p a₁ b₁ A₁ h₁ ψ₁ := by rw [S4_cross_swap,hcross₁]
  have hdt : inner ℝ (SphereGeom.cross (capAxis p a₁ A₁) (capExitPoint p a₁ b₁ A₁ h₁ ψ₁))
      (SphereGeom.cross (capAxis p a₂ A₂) (capExitPoint p a₁ b₁ A₁ h₁ ψ₁))=
      rayRadical A₁ h₁ ψ₁*rayRadical A₂ h₂ ψ₂+
        (capBeta A₁*Real.sin ψ₁)*(capBeta A₂*Real.sin ψ₂) := by
    rw [htan₁,htan₂']
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      hrr₁,hss₁,hrs₁,hsr₁]
    ring
  have hct : inner ℝ (capExitPoint p a₁ b₁ A₁ h₁ ψ₁)
      (SphereGeom.cross (SphereGeom.cross (capAxis p a₁ A₁) (capExitPoint p a₁ b₁ A₁ h₁ ψ₁))
        (SphereGeom.cross (capAxis p a₂ A₂) (capExitPoint p a₁ b₁ A₁ h₁ ψ₁)))=
      rayRadical A₁ h₁ ψ₁*(capBeta A₂*Real.sin ψ₂)-
        (capBeta A₁*Real.sin ψ₁)*rayRadical A₂ h₂ ψ₂ := by
    rw [htan₁,htan₂']
    simp only [S4_cross_linear_left,S4_cross_linear_right,A4_cross_smul_left,S4_cross_smul_right,
      S4_cross_self,hcross₁,hswap,smul_zero,zero_add,add_zero,
      inner_add_right,real_inner_smul_right,inner_neg_right,hu₁]
    ring
  rcases A4_tail_trig A₁ h₁ ψ₁ hh₁ hA₁ hA₁1 with ⟨hk₁,hx₁,hco₁⟩
  rcases A4_tail_trig A₂ h₂ ψ₂ hh₂ hA₂ hA₂1 with ⟨hk₂,hx₂,hco₂⟩
  have he : (⟨rayRadical A₁ h₁ ψ₁*rayRadical A₂ h₂ ψ₂+
        (capBeta A₁*Real.sin ψ₁)*(capBeta A₂*Real.sin ψ₂),
      rayRadical A₁ h₁ ψ₁*(capBeta A₂*Real.sin ψ₂)-
        (capBeta A₁*Real.sin ψ₁)*rayRadical A₂ h₂ ψ₂⟩ : ℂ)=
      (↑(capK h₁*capK h₂) : ℂ)*
      ⟨Real.sqrt (1-(capBeta A₁*Real.sin ψ₁/capK h₁)^2)*
          Real.sqrt (1-(capBeta A₂*Real.sin ψ₂/capK h₂)^2)+
        (capBeta A₁*Real.sin ψ₁/capK h₁)*(capBeta A₂*Real.sin ψ₂/capK h₂),
        Real.sqrt (1-(capBeta A₁*Real.sin ψ₁/capK h₁)^2)*(capBeta A₂*Real.sin ψ₂/capK h₂)-
        (capBeta A₁*Real.sin ψ₁/capK h₁)*Real.sqrt (1-(capBeta A₂*Real.sin ψ₂/capK h₂)^2)⟩ := by
    rw [hco₁,hco₂]
    apply Complex.ext <;> simp only [Complex.ofReal_mul,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,zero_add]
    all_goals field_simp [hk₁.ne',hk₂.ne'] <;> ring
  unfold capCorner
  rw [hdt,hct,he,Complex.arg_real_mul _ (mul_pos hk₁ hk₂)]
  exact A4_asin_turn _ _ hx₁ hx₂
#print axioms proof_SolidGeom_CapPolar_cap_corner_tail_angle
