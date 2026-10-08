import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame_period
set_option autoImplicit false
open MeasureTheory SphereGeom
noncomputable section
set_option maxHeartbeats 1800000
private theorem ip (a b p : E3) (h : Orthonormal ℝ ![a,b,p]) (x y : ℝ) :
    inner ℝ (Real.cos x • a + Real.sin x • b) (Real.cos y • a + Real.sin y • b) =
      Real.cos (x-y) := by
  have haa : inner ℝ a a = 1 := by simpa using (orthonormal_iff_ite.mp h (0 : Fin 3) 0)
  have hbb : inner ℝ b b = 1 := by simpa using (orthonormal_iff_ite.mp h (1 : Fin 3) 1)
  have hab : inner ℝ a b = 0 := by simpa using (orthonormal_iff_ite.mp h (0 : Fin 3) 1)
  have hba : inner ℝ b a = 0 := by simpa using (orthonormal_iff_ite.mp h (1 : Fin 3) 0)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real, haa,hbb,hab,hba, mul_one,mul_zero,add_zero,zero_add, Real.cos_sub]
  ring
private theorem sqrtSin (x : ℝ) : Real.sqrt (1-Real.cos x^2) = |Real.sin x| := by
  rw [show 1-Real.cos x^2 = Real.sin x^2 by nlinarith [Real.sin_sq_add_cos_sq x], Real.sqrt_sq_eq_abs]
theorem proof_SphereGeom_Aux_Pair_orthogonal_frame_kernel (a b p : E3) (hab : Orthonormal ℝ ![a,b,p]) :
    (∀ s t : ℝ, Real.sqrt (1-(inner ℝ (Real.cos s • a + Real.sin s • b)
      (Real.cos t • a + Real.sin t • b))^2) = |Real.sin (s-t)|) ∧
    (∀ (u c d : E3) (hcd : Orthonormal ℝ ![c,d,u]) (t : ℝ)
      (hp : p = Real.cos t • c + Real.sin t • d) (f : E3 → ENNReal) (hf : Measurable f),
      (∫⁻ v in Set.Ioc 0 (2*Real.pi),
        f (Real.cos v • a + Real.sin v • b) * ENNReal.ofReal (Real.sqrt
          (1-(inner ℝ u (Real.cos v • a + Real.sin v • b))^2))) =
      ∫⁻ v in Set.Ioc 0 (2*Real.pi),
        f (Real.cos v • u + Real.sin v • (-Real.sin t • c + Real.cos t • d)) *
          ENNReal.ofReal |Real.sin v|) := by
  constructor
  · intro s t
    rw [ip a b p hab s t, sqrtSin]
  · intro u c d hcd t hp f hf
    let k : E3 := -Real.sin t • c + Real.cos t • d
    have hcc : inner ℝ c c = 1 := by simpa using (orthonormal_iff_ite.mp hcd (0 : Fin 3) 0)
    have hdd : inner ℝ d d = 1 := by simpa using (orthonormal_iff_ite.mp hcd (1 : Fin 3) 1)
    have huu : inner ℝ u u = 1 := by simpa using (orthonormal_iff_ite.mp hcd (2 : Fin 3) 2)
    have hccross : inner ℝ c d = 0 := by simpa using (orthonormal_iff_ite.mp hcd (0 : Fin 3) 1)
    have hdcross : inner ℝ d c = 0 := by simpa using (orthonormal_iff_ite.mp hcd (1 : Fin 3) 0)
    have hcu : inner ℝ c u = 0 := by simpa using (orthonormal_iff_ite.mp hcd (0 : Fin 3) 2)
    have hdu : inner ℝ d u = 0 := by simpa using (orthonormal_iff_ite.mp hcd (1 : Fin 3) 2)
    have huc : inner ℝ u c = 0 := by simpa using (orthonormal_iff_ite.mp hcd (2 : Fin 3) 0)
    have hud : inner ℝ u d = 0 := by simpa using (orthonormal_iff_ite.mp hcd (2 : Fin 3) 1)
    have hrot : Orthonormal ℝ ![u,k,p] := by
      apply orthonormal_iff_ite.mpr
      intro i j
      rw [hp]
      fin_cases i <;> fin_cases j
      all_goals first
        | change inner ℝ u u = 1
        | change inner ℝ u k = 0
        | change inner ℝ u (Real.cos t • c + Real.sin t • d) = 0
        | change inner ℝ k u = 0
        | change inner ℝ k k = 1
        | change inner ℝ k (Real.cos t • c + Real.sin t • d) = 0
        | change inner ℝ (Real.cos t • c + Real.sin t • d) u = 0
        | change inner ℝ (Real.cos t • c + Real.sin t • d) k = 0
        | change inner ℝ (Real.cos t • c + Real.sin t • d) (Real.cos t • c + Real.sin t • d) = 1
      all_goals simp only [k,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
        RCLike.conj_to_real,hcc,hdd,huu,hccross,hdcross,hcu,hdu,huc,hud,
        mul_one,mul_zero,add_zero,zero_add]
      all_goals nlinarith [Real.sin_sq_add_cos_sq t]
    let F : E3 → ENNReal := fun v => f v * ENNReal.ofReal (Real.sqrt (1-(inner ℝ u v)^2))
    have hF : Measurable F := by dsimp [F]; fun_prop
    have hmeasure := SphereGeom.Aux.Pair.arcMeasure_greatCircle_frame_period a b p hab
    have hmeasure' := SphereGeom.Aux.Pair.arcMeasure_greatCircle_frame_period u k p hrot
    have heq : (∫⁻ v in Set.Ico 0 (2*Real.pi), F (circlePt 0 a b 1 v)) =
        ∫⁻ v in Set.Ico 0 (2*Real.pi), F (circlePt 0 u k 1 v) := by
      calc
        _ = ∫⁻ x, F x ∂arcMeasure.restrict (greatCircle p) := by
          rw [hmeasure,lintegral_map hF (by unfold circlePt; fun_prop)]
        _ = _ := by
          rw [hmeasure',lintegral_map hF (by unfold circlePt; fun_prop)]
    rw [← restrict_Ico_eq_restrict_Ioc]
    calc
      _ = _ := by simpa [F,circlePt] using heq
      _ = _ := by
        apply lintegral_congr
        intro v
        have huk : inner ℝ u k = 0 := by simpa using (orthonormal_iff_ite.mp hrot (0 : Fin 3) 1)
        simp only [F,inner_add_right,inner_smul_right,huu,huk,mul_one,mul_zero,add_zero,sqrtSin]
        rfl
