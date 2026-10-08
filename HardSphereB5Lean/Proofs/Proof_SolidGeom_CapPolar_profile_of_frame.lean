import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_frameExitRadius
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
open scoped RealInnerProductSpace
set_option maxHeartbeats 1000000

private lemma SolidGeom.CapPolar.FP_exit_properties (A h B : ℝ) (hh : 0 < h) (ha : h < A) :
    0 < frameExitSin A h B ∧
    (frameExitCos A h B)^2 + (frameExitSin A h B)^2 = 1 ∧
    A*frameExitCos A h B+B*frameExitSin A h B=h := by
  let D := A^2+B^2
  let R := Real.sqrt (D-h^2)
  have hA : 0 < A := hh.trans ha
  have hd : 0 < D := by dsimp [D]; nlinarith [sq_nonneg B]
  have hrd : 0 < D-h^2 := by dsimp [D]; nlinarith [sq_nonneg B]
  have hr : 0 < R := Real.sqrt_pos.mpr hrd
  have hr2 : R^2 = D-h^2 := Real.sq_sqrt hrd.le
  have hf : (A*R)^2-(B*h)^2 = D*(A^2-h^2) := by
    rw [mul_pow,hr2]; dsimp [D]; ring
  have hprod : 0 < D*(A^2-h^2) := mul_pos hd (by nlinarith)
  have hnum : 0 < B*h+A*R := by nlinarith [mul_pos hA hr]
  have hS : 0 < frameExitSin A h B := div_pos hnum hd
  refine ⟨hS,?_,?_⟩
  · unfold frameExitCos frameExitSin
    change ((A*h-B*R)/D)^2+((B*h+A*R)/D)^2=1
    rw [div_pow,div_pow,← add_div]
    apply (div_eq_one_iff_eq (pow_ne_zero 2 hd.ne')).mpr
    calc
      _ = D*(h^2+R^2) := by dsimp [D]; ring
      _ = D^2 := by rw [hr2]; ring
  · unfold frameExitCos frameExitSin
    change A*((A*h-B*R)/D)+B*((B*h+A*R)/D)=h
    field_simp [hd.ne']
    dsimp [D]
    ring

private lemma SolidGeom.CapPolar.FP_exit_bound (A h B : ℝ) (hh : 0 < h) (ha : h < A) :
    -1 < frameExitCos A h B ∧ frameExitCos A h B < 1 := by
  obtain ⟨hS,hunit,_⟩ := FP_exit_properties A h B hh ha
  constructor <;> nlinarith [sq_pos_of_pos hS]

private lemma SolidGeom.CapPolar.FP_radius_trig (A h B : ℝ) (hh : 0 < h) (ha : h < A) :
    Real.cos (frameExitRadius A h B)=frameExitCos A h B ∧
    Real.sin (frameExitRadius A h B)=frameExitSin A h B := by
  have hb := FP_exit_bound A h B hh ha
  obtain ⟨hS,hu,_⟩ := FP_exit_properties A h B hh ha
  constructor
  · exact Real.cos_arccos hb.1.le hb.2.le
  · unfold frameExitRadius
    rw [Real.sin_arccos,show 1-(frameExitCos A h B)^2=(frameExitSin A h B)^2 by linarith,
      Real.sqrt_sq_eq_abs,abs_of_pos hS]

private lemma SolidGeom.CapPolar.FP_radius_continuous (A h : ℝ) (hh : 0 < h) (ha : h < A) :
    Continuous (frameExitRadius A h) := by
  have ha0 : 0 < A := hh.trans ha
  unfold frameExitRadius frameExitCos
  apply Real.continuous_arccos.comp
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro B
    nlinarith [sq_nonneg B]

theorem proof_SolidGeom_CapPolar_profile_of_frame
    (e:Fin 3→SphereGeom.E3) (he:Orthonormal ℝ e)
    (n:Fin 3→SphereGeom.E3) (hn:∀j,‖n j‖=1) (h:Fin 3→ℝ)
    (hh:∀ j, 0 < h j) (hp:∀j,h j < inner ℝ (n j) (e 2)):
    ∃ P :SolidGeom.CapPolar.Profile,P.e=e ∧ P.normal=n ∧ P.height=h ∧
      ∀ j ψ,P.rho j ψ=SolidGeom.CapPolar.frameExitRadius (inner ℝ (n j) (e 2)) (h j)
        (Real.cos ψ*inner ℝ (n j) (e 0)+Real.sin ψ*inner ℝ (n j) (e 1)) := by
  let rho : Fin 3 → ℝ → ℝ := fun j ψ => frameExitRadius (inner ℝ (n j) (e 2)) (h j)
    (Real.cos ψ*inner ℝ (n j) (e 0)+Real.sin ψ*inner ℝ (n j) (e 1))
  have hrcont : ∀ j, Continuous (rho j) := by
    intro j
    exact (FP_radius_continuous _ _ (hh j) (hp j)).comp (by fun_prop)
  have hrrange : ∀ j ψ, 0 < rho j ψ ∧ rho j ψ < Real.pi := by
    intro j ψ
    have hb := FP_exit_bound (inner ℝ (n j) (e 2)) (h j)
      (Real.cos ψ*inner ℝ (n j) (e 0)+Real.sin ψ*inner ℝ (n j) (e 1)) (hh j) (hp j)
    exact ⟨Real.arccos_pos.mpr hb.2,Real.arccos_lt_pi.mpr hb.1⟩
  have hrroot : ∀ j ψ, inner ℝ (n j) (polar e (rho j ψ) ψ) = h j := by
    intro j ψ
    have ht := FP_radius_trig (inner ℝ (n j) (e 2)) (h j)
      (Real.cos ψ*inner ℝ (n j) (e 0)+Real.sin ψ*inner ℝ (n j) (e 1)) (hh j) (hp j)
    have hr := (FP_exit_properties (inner ℝ (n j) (e 2)) (h j)
      (Real.cos ψ*inner ℝ (n j) (e 0)+Real.sin ψ*inner ℝ (n j) (e 1)) (hh j) (hp j)).2.2
    unfold polar
    simp only [inner_add_right,real_inner_smul_right]
    change Real.sin (rho j ψ)*Real.cos ψ*inner ℝ (n j) (e 0)+
      Real.sin (rho j ψ)*Real.sin ψ*inner ℝ (n j) (e 1)+
      Real.cos (rho j ψ)*inner ℝ (n j) (e 2)=h j
    dsimp [rho]
    rw [ht.1,ht.2]
    nlinarith [hr]
  refine ⟨⟨e,he,n,hn,h,hh,hp,rho,hrcont,hrrange,hrroot⟩,rfl,rfl,rfl,?_⟩
  intro j ψ
  rfl
#print axioms proof_SolidGeom_CapPolar_profile_of_frame
