import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_signed_cylinder_map
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
noncomputable section
private theorem chart_norm_sq (a b c : ℝ) :
    ‖a • e1 + b • e2 + c • e‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, e, e1, e2, Fin.sum_univ_succ]
  ring

private theorem sphereMeasure_translate (c : Pt) :
    sphereMeasure c = dOmega.map (fun u => c+u) := by
  unfold dOmega sphereMeasure
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, zero_add]

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_signed_endpoint_measures :
    ((sphereMeasure 0).restrict FA =
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Icc (1/2 : ℝ) 1 ×ˢ Set.Icc (-Real.pi) Real.pi)).map
        (fun x : ℝ × ℝ => endpointCylinder x.1 x.2)) ∧
    ((sphereMeasure e).restrict FB =
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Icc (-1 : ℝ) (-1/2) ×ˢ Set.Icc (-Real.pi) Real.pi)).map
        (fun x : ℝ × ℝ => e + endpointCylinder x.1 x.2))  := by
  let r : ℝ → ℝ := fun z => Real.sqrt (1-z^2)
  let CA : ℝ × ℝ → Pt := fun x => endpointCylinder x.1 x.2
  let CB : ℝ × ℝ → Pt := fun x => e+endpointCylinder x.1 x.2
  let S : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-Real.pi) Real.pi
  let ZA : Set (ℝ × ℝ) := Set.Icc (1/2 : ℝ) 1 ×ˢ Set.Icc (-Real.pi) Real.pi
  let ZB : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) (-1/2) ×ˢ Set.Icc (-Real.pi) Real.pi
  have hCA : Measurable CA := by dsimp [CA,endpointCylinder]; fun_prop
  have hCB : Measurable CB := by dsimp [CB,endpointCylinder]; fun_prop
  have hrad (x : ℝ × ℝ) (hx : x ∈ S) : 0 ≤ 1-x.1^2 := by
    have h1 : 0 ≤ 1-x.1 := by linarith [hx.1.2]
    have h2 : 0 ≤ 1+x.1 := by linarith [hx.1.1]
    nlinarith [mul_nonneg h1 h2]
  have hcirc (x : ℝ × ℝ) (hx : x ∈ S) :
      (r x.1 * Real.cos x.2)^2 + (r x.1 * Real.sin x.2)^2 = 1-x.1^2 := by
    simp only [mul_pow, r, Real.sq_sqrt (hrad x hx)]
    nlinarith [congrArg (fun t : ℝ => (1-x.1^2)*t) (Real.sin_sq_add_cos_sq x.2)]
  have hdistA (x : ℝ × ℝ) (hx : x ∈ S) :
      ‖CA x‖^2 = 1 ∧ ‖CA x-e‖^2 = 2-2*x.1 := by
    constructor
    · change ‖(r x.1*Real.cos x.2)•e1 + (r x.1*Real.sin x.2)•e2 + x.1•e‖^2=1
      rw [chart_norm_sq]; nlinarith [hcirc x hx]
    · have hh : CA x-e = (r x.1*Real.cos x.2)•e1 +
          (r x.1*Real.sin x.2)•e2 + (x.1-1)•e := by dsimp [CA, endpointCylinder,r]; module
      rw [hh, chart_norm_sq]; nlinarith [hcirc x hx]
  have hdistB (x : ℝ × ℝ) (hx : x ∈ S) :
      ‖CB x-e‖^2 = 1 ∧ ‖CB x‖^2 = 2+2*x.1 := by
    constructor
    · have hh : CB x-e=CA x := by dsimp [CA,CB]; abel
      rw [hh]; exact (hdistA x hx).1
    · have hh : CB x = (r x.1*Real.cos x.2)•e1 +
          (r x.1*Real.sin x.2)•e2 + (x.1+1)•e := by dsimp [CB,endpointCylinder,r]; module
      rw [hh, chart_norm_sq]; nlinarith [hcirc x hx]
  have hpreA : CA ⁻¹' FA ∩ S = ZA := by
    ext x
    constructor
    · rintro ⟨hFA,hxS⟩
      have hn : ‖CA x-e‖ ≤ 1 := by simpa [FA,Metric.mem_closedBall,dist_eq_norm] using hFA.2
      exact ⟨⟨by nlinarith [(hdistA x hxS).2,norm_nonneg (CA x-e)],hxS.1.2⟩,hxS.2⟩
    · intro hxZ
      have hxS : x∈S := ⟨⟨by linarith [hxZ.1.1],hxZ.1.2⟩,hxZ.2⟩
      refine ⟨?_,hxS⟩
      constructor
      · change dist (CA x) 0=1
        rw [dist_zero_right]; nlinarith [(hdistA x hxS).1,norm_nonneg (CA x)]
      · change dist (CA x) e ≤1
        rw [dist_eq_norm]; nlinarith [(hdistA x hxS).2,norm_nonneg (CA x-e),hxZ.1.1]
  have hpreB : CB ⁻¹' FB ∩ S = ZB := by
    ext x
    constructor
    · rintro ⟨hFB,hxS⟩
      have hn : ‖CB x‖ ≤1 := by simpa [FB,Metric.mem_closedBall,dist_zero_right] using hFB.2
      exact ⟨⟨hxS.1.1,by nlinarith [(hdistB x hxS).2,norm_nonneg (CB x)]⟩,hxS.2⟩
    · intro hxZ
      have hxS : x∈S := ⟨⟨hxZ.1.1,by linarith [hxZ.1.2]⟩,hxZ.2⟩
      refine ⟨?_,hxS⟩
      constructor
      · change dist (CB x) e=1
        rw [dist_eq_norm]; nlinarith [(hdistB x hxS).1,norm_nonneg (CB x-e)]
      · change dist (CB x) 0≤1
        rw [dist_zero_right]; nlinarith [(hdistB x hxS).2,norm_nonneg (CB x),hxZ.1.2]
  have hmapA : sphereMeasure 0 = (volume.restrict S).map CA := by
    exact HardSphereB5.SphericalCrofton.Aux.Coarea.signed_cylinder_map
  have hmapB : sphereMeasure e = (volume.restrict S).map CB := by
    rw [sphereMeasure_translate,HardSphereB5.SphericalCrofton.Aux.Coarea.signed_cylinder_map,
      Measure.map_map (by fun_prop) hCA]
    rfl
  have hFA : MeasurableSet FA := (Metric.isClosed_sphere.inter Metric.isClosed_closedBall).measurableSet
  have hFB : MeasurableSet FB := (Metric.isClosed_sphere.inter Metric.isClosed_closedBall).measurableSet
  constructor
  · rw [hmapA,Measure.restrict_map hCA hFA,Measure.restrict_restrict (hFA.preimage hCA),hpreA]
  · rw [hmapB,Measure.restrict_map hCB hFB,Measure.restrict_restrict (hFB.preimage hCB),hpreB]

