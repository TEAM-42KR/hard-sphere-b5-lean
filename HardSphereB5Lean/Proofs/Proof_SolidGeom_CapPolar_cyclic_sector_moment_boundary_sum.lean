import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_sector_moment_primitive
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

private lemma SolidGeom.CapPolar.momentPrimitive_boundary_form (p a b : E3) (A h ψ : ℝ)
    (hp : inner ℝ p p=1) (ha : inner ℝ a a=1) (hpa : inner ℝ p a=0)
    (hb : SphereGeom.cross p a=b) :
    momentPrimitive p a b A h ψ =
      ((1-h^2)*momentAzimuth A h ψ/2) • SolidGeom.CapPolar.capAxis p a A +
      (h/2) • SphereGeom.cross (SolidGeom.CapPolar.capAxis p a A) (SolidGeom.CapPolar.capExitPoint p a b A h ψ) -
      SolidGeom.CapPolar.radialEdgeCorrection p a b A h ψ := by
  have hpb : SphereGeom.cross p b= -a := by
    rw [← hb,SphereGeom.cross_vec_triple,hp,hpa]
    simp
  have hab : SphereGeom.cross a b=p := by
    rw [← hb,SphereGeom.cross_vec_triple,ha,hpa]
    simp
  have hap : SphereGeom.cross a p= -b := by rw [S4_cross_swap,hb]
  unfold SolidGeom.CapPolar.radialEdgeCorrection SolidGeom.CapPolar.capAxis SolidGeom.CapPolar.capExitPoint SolidGeom.CapPolar.capDirection
  simp only [S4_cross_linear_left,S4_cross_linear_right,S4_cross_self,hb,hpb,hab,hap]
  unfold momentPrimitive
  simp only [smul_zero,zero_smul,zero_add,add_zero]
  ext k
  simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,PiLp.neg_apply,smul_eq_mul]
  ring

private lemma S4_inner_exitPoint (p a b : E3) (A h ψ : ℝ)
    (hp : inner ℝ p p=1) (hpa : inner ℝ p a=0) (hpb : inner ℝ p b=0) :
    inner ℝ p (SolidGeom.CapPolar.capExitPoint p a b A h ψ)=exitCos A h ψ := by
  simp only [SolidGeom.CapPolar.capExitPoint,SolidGeom.CapPolar.capDirection,inner_add_right,real_inner_smul_right,hp,hpa,hpb,
    mul_zero,mul_one,zero_add,add_zero]

private lemma SolidGeom.CapPolar.radial_correction_endpoint (p a b : E3) (A h ψ : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1)
    (hp : inner ℝ p p=1) (hpa : inner ℝ p a=0) (hpb : inner ℝ p b=0) :
    SolidGeom.CapPolar.radialEdgeCorrection p a b A h ψ=SolidGeom.CapPolar.radialEdgeCorrectionOfPoint p (SolidGeom.CapPolar.capExitPoint p a b A h ψ) := by
  unfold SolidGeom.CapPolar.radialEdgeCorrectionOfPoint
  rw [S4_inner_exitPoint p a b A h ψ hp hpa hpb]
  have hsq : 1-exitCos A h ψ^2=exitSin A h ψ^2 := by
    linarith [S3_CS_unit A h ψ hh hA hA1]
  rw [hsq,Real.sqrt_sq_eq_abs,abs_of_pos (S3_S_pos A h ψ hh hA hA1)]
  unfold SolidGeom.CapPolar.capExitPoint
  rw [S4_cross_linear_right,S4_cross_self,smul_zero,zero_add]
  unfold SolidGeom.CapPolar.radialEdgeCorrection exitRadius
  rw [smul_smul]
  congr 1
  field_simp [(S3_S_pos A h ψ hh hA hA1).ne']

private lemma SolidGeom.CapPolar.sector_moment_boundary_form (p a b : E3) (A h α ω : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1)
    (hf : Orthonormal ℝ (fun k : Fin 3 => ![p,a,b] k))
    (hp : inner ℝ p p=1) (ha : inner ℝ a a=1) (hpa : inner ℝ p a=0)
    (hb : SphereGeom.cross p a=b) :
    (∫ ψ in α..ω, ∫ ρ in (0)..(exitRadius A h ψ), Real.sin ρ • polarRay p a b ψ ρ) =
      ((1-h^2)*(momentAzimuth A h ω-momentAzimuth A h α)/2) • SolidGeom.CapPolar.capAxis p a A +
      (h/2) • SphereGeom.cross (SolidGeom.CapPolar.capAxis p a A)
        (SolidGeom.CapPolar.capExitPoint p a b A h ω-SolidGeom.CapPolar.capExitPoint p a b A h α) -
      (SolidGeom.CapPolar.radialEdgeCorrection p a b A h ω-SolidGeom.CapPolar.radialEdgeCorrection p a b A h α) := by
  rw [SolidGeom.CapPolar.sector_moment_primitive p a b A h α ω hh hA hA1 hf,
    SolidGeom.CapPolar.momentPrimitive_boundary_form p a b A h ω hp ha hpa hb,
    SolidGeom.CapPolar.momentPrimitive_boundary_form p a b A h α hp ha hpa hb,S4_cross_sub]
  module
private lemma SolidGeom.CapPolar.radial_edges_telescope (n : ℕ) (p : E3)
    (a b : Fin (n+1) → E3) (A h α ω : Fin (n+1) → ℝ)
    (hh : ∀ j, 0<h j) (hA : ∀ j, h j<A j) (hA1 : ∀ j, A j≤1)
    (hp : inner ℝ p p=1) (hpa : ∀ j, inner ℝ p (a j)=0)
    (hpb : ∀ j, inner ℝ p (b j)=0)
    (hglue : ∀ j, SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (ω j) =
      SolidGeom.CapPolar.capExitPoint p (a (j+1)) (b (j+1)) (A (j+1)) (h (j+1)) (α (j+1))) :
    ∑ j, (SolidGeom.CapPolar.radialEdgeCorrection p (a j) (b j) (A j) (h j) (ω j)-
      SolidGeom.CapPolar.radialEdgeCorrection p (a j) (b j) (A j) (h j) (α j))=0 := by
  let E := fun j => SolidGeom.CapPolar.radialEdgeCorrection p (a j) (b j) (A j) (h j) (ω j)
  let S := fun j => SolidGeom.CapPolar.radialEdgeCorrection p (a j) (b j) (A j) (h j) (α j)
  have hES : ∀ j, E j=S (j+1) := by
    intro j
    change SolidGeom.CapPolar.radialEdgeCorrection p (a j) (b j) (A j) (h j) (ω j)=
      SolidGeom.CapPolar.radialEdgeCorrection p (a (j+1)) (b (j+1)) (A (j+1)) (h (j+1)) (α (j+1))
    rw [SolidGeom.CapPolar.radial_correction_endpoint p (a j) (b j) (A j) (h j) (ω j)
      (hh j) (hA j) (hA1 j) hp (hpa j) (hpb j),
      SolidGeom.CapPolar.radial_correction_endpoint p (a (j+1)) (b (j+1)) (A (j+1)) (h (j+1)) (α (j+1))
      (hh (j+1)) (hA (j+1)) (hA1 (j+1)) hp (hpa (j+1)) (hpb (j+1)),hglue]
  have hperm : (∑ j : Fin (n+1), S (j+1))=∑ j : Fin (n+1), S j := by
    exact Fintype.sum_equiv (Equiv.addRight (1 : Fin (n+1))) _ _ (fun j => rfl)
  change (∑ j : Fin (n+1), (E j-S j))=0
  rw [Finset.sum_sub_distrib]
  simp_rw [hES]
  rw [hperm,sub_self]

theorem proof_SolidGeom_CapPolar_cyclic_sector_moment_boundary_sum (n : ℕ) (p : E3)
    (a b : Fin (n+1) → E3) (A h α ω : Fin (n+1) → ℝ)
    (hh : ∀ j, 0<h j) (hA : ∀ j, h j<A j) (hA1 : ∀ j, A j≤1)
    (hf : ∀ j, Orthonormal ℝ (fun k : Fin 3 => ![p,a j,b j] k))
    (hp : inner ℝ p p=1) (ha : ∀ j, inner ℝ (a j) (a j)=1)
    (hpa : ∀ j, inner ℝ p (a j)=0) (hpb : ∀ j, inner ℝ p (b j)=0)
    (hb : ∀ j, SphereGeom.cross p (a j)=b j)
    (hglue : ∀ j, SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (ω j) =
      SolidGeom.CapPolar.capExitPoint p (a (j+1)) (b (j+1)) (A (j+1)) (h (j+1)) (α (j+1))) :
    (∑ j, ∫ ψ in (α j)..(ω j), ∫ ρ in (0)..(exitRadius (A j) (h j) ψ),
      Real.sin ρ • polarRay p (a j) (b j) ψ ρ) =
    ∑ j, (((1-(h j)^2)*
        (momentAzimuth (A j) (h j) (ω j)-momentAzimuth (A j) (h j) (α j))/2) •
          SolidGeom.CapPolar.capAxis p (a j) (A j) +
      (h j/2) • SphereGeom.cross (SolidGeom.CapPolar.capAxis p (a j) (A j))
        (SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (ω j)-
          SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (α j))) := by
  have ht := SolidGeom.CapPolar.radial_edges_telescope n p a b A h α ω hh hA hA1 hp hpa hpb hglue
  calc
    _ = ∑ j, (((1-(h j)^2)*
        (momentAzimuth (A j) (h j) (ω j)-momentAzimuth (A j) (h j) (α j))/2) •
          SolidGeom.CapPolar.capAxis p (a j) (A j) +
      (h j/2) • SphereGeom.cross (SolidGeom.CapPolar.capAxis p (a j) (A j))
        (SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (ω j)-
          SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (α j)) -
      (SolidGeom.CapPolar.radialEdgeCorrection p (a j) (b j) (A j) (h j) (ω j)-SolidGeom.CapPolar.radialEdgeCorrection p (a j) (b j) (A j) (h j) (α j))) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact SolidGeom.CapPolar.sector_moment_boundary_form p (a j) (b j) (A j) (h j) (α j) (ω j)
          (hh j) (hA j) (hA1 j) (hf j) hp (ha j) (hpa j) (hb j)
    _ = _ := by rw [Finset.sum_sub_distrib,ht,sub_zero]
