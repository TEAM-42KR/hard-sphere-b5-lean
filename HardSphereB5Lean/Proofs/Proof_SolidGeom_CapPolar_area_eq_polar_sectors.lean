import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_Profile
import HardSphereB5Lean.Theorems.Thm_SphereGeom_integral_dOmega_frame
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000

private def SolidGeom.CapPolar.rayGauge (a h t : ℝ) : ℝ := (h-a*Real.cos t)/Real.sin t

private lemma SolidGeom.CapPolar.rayGauge_hasDerivAt (a h t : ℝ) (ht : t ∈ Set.Ioo 0 Real.pi) :
    HasDerivAt (SolidGeom.CapPolar.rayGauge a h)
      ((a-h*Real.cos t)/(Real.sin t)^2) t := by
  have hs : Real.sin t ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  have hd := ((hasDerivAt_const t h).sub ((Real.hasDerivAt_cos t).const_mul a)).div
    (Real.hasDerivAt_sin t) hs
  have he : (((0-a*(-Real.sin t))*Real.sin t-(h-a*Real.cos t)*Real.cos t)/(Real.sin t)^2) =
      (a-h*Real.cos t)/(Real.sin t)^2 := by
    congr 1
    have hc := Real.sin_sq_add_cos_sq t
    linear_combination a*hc
  have hf : (((fun x : ℝ => h)-(fun y => a*Real.cos y))/Real.sin) =
      SolidGeom.CapPolar.rayGauge a h := rfl
  simpa only [hf,Pi.sub_apply,he] using hd

private lemma SolidGeom.CapPolar.rayGauge_strictMono (a h : ℝ) (hh : 0 < h) (ha : h < a) :
    StrictMonoOn (SolidGeom.CapPolar.rayGauge a h) (Set.Ioo 0 Real.pi) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0:ℝ) Real.pi)
  · exact ((continuous_const.sub (continuous_const.mul Real.continuous_cos)).continuousOn).div
      Real.continuous_sin.continuousOn (fun t ht => ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(SolidGeom.CapPolar.rayGauge_hasDerivAt a h t ht).deriv]
    apply div_pos
    · have hc := Real.cos_le_one t
      nlinarith
    · exact sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)

private lemma SolidGeom.CapPolar.ray_cap_iff (a b h ρ t : ℝ) (hh : 0 < h) (ha : h < a)
    (hρ : ρ ∈ Set.Ioo 0 Real.pi) (hroot : a*Real.cos ρ+b*Real.sin ρ=h)
    (ht : t ∈ Set.Icc 0 Real.pi) : h ≤ a*Real.cos t+b*Real.sin t ↔ t ≤ ρ := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0,Real.cos_zero,Real.sin_zero]
    simp only [mul_one,mul_zero,add_zero]
    exact iff_of_true ha.le hρ.1.le
  rcases eq_or_lt_of_le ht.2 with hπ | hπ
  · rw [hπ,Real.cos_pi,Real.sin_pi]
    constructor <;> intro h <;> nlinarith [hρ.2]
  have hsin := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hsinρ := Real.sin_pos_of_pos_of_lt_pi hρ.1 hρ.2
  have hr : SolidGeom.CapPolar.rayGauge a h ρ = b := by
    unfold SolidGeom.CapPolar.rayGauge
    apply (div_eq_iff (ne_of_gt hsinρ)).mpr
    linarith
  have hmono := SolidGeom.CapPolar.rayGauge_strictMono a h hh ha
  have hle : SolidGeom.CapPolar.rayGauge a h t ≤ b ↔ t ≤ ρ := by
    rw [← hr]
    exact hmono.le_iff_le ⟨h0,hπ⟩ hρ
  rw [← hle]
  unfold SolidGeom.CapPolar.rayGauge
  rw [div_le_iff₀ hsin]
  constructor <;> intro h <;> linarith

private lemma SolidGeom.CapPolar.polar_norm (e : Fin 3 → E3) (he : Orthonormal ℝ e) (t φ : ℝ) :
    ‖SolidGeom.CapPolar.polar e t φ‖ = 1 := by
  have hinner := orthonormal_iff_ite.mp he
  have hsq : ‖SolidGeom.CapPolar.polar e t φ‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold SolidGeom.CapPolar.polar
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,hinner]
    simp
    linear_combination (Real.sin t)^2*(Real.sin_sq_add_cos_sq φ)+(Real.sin_sq_add_cos_sq t)
  nlinarith [norm_nonneg (SolidGeom.CapPolar.polar e t φ)]

private lemma SolidGeom.CapPolar.winner_min (P : Profile) (φ : ℝ) :
    ∀ j : Fin 3, SolidGeom.CapPolar.radius P φ ≤ P.rho j φ := by
  unfold SolidGeom.CapPolar.radius SolidGeom.CapPolar.winner
  split_ifs with h0 h1
  · intro j
    fin_cases j
    · exact le_rfl
    · exact h0.1
    · exact h0.2
  · intro j
    fin_cases j
    · by_contra hn
      exact h0 ⟨(lt_of_not_ge hn).le,((lt_of_not_ge hn).le.trans h1)⟩
    · exact le_rfl
    · exact h1
  · have h21 : P.rho 2 φ ≤ P.rho 1 φ := (le_of_not_ge h1)
    intro j
    fin_cases j
    · by_contra hn
      exact h0 ⟨(lt_of_not_ge hn).le.trans h21,(lt_of_not_ge hn).le⟩
    · exact h21
    · exact le_rfl

private lemma SolidGeom.CapPolar.ray_membership (P : Profile) (t φ : ℝ)
    (ht : t ∈ Set.Icc 0 Real.pi) :
    SolidGeom.CapPolar.polar P.e t φ ∈ SolidGeom.CapPolar.caps P ↔
      t ≤ SolidGeom.CapPolar.radius P φ := by
  have hcap : ∀ j, P.height j ≤ inner ℝ (P.normal j) (SolidGeom.CapPolar.polar P.e t φ) ↔
      t ≤ P.rho j φ := by
    intro j
    let a := inner ℝ (P.normal j) (P.e 2)
    let b := Real.cos φ*inner ℝ (P.normal j) (P.e 0)+Real.sin φ*inner ℝ (P.normal j) (P.e 1)
    have hroot : a*Real.cos (P.rho j φ)+b*Real.sin (P.rho j φ)=P.height j := by
      have hr := P.ray_boundary j φ
      unfold SolidGeom.CapPolar.polar at hr
      simp only [inner_add_right,real_inner_smul_right] at hr
      dsimp [a,b]
      nlinarith [hr]
    have he := SolidGeom.CapPolar.ray_cap_iff a b (P.height j) (P.rho j φ) t
      (P.height_pos j) (P.pole_inside j) (P.rho_range j φ) hroot ht
    unfold SolidGeom.CapPolar.polar
    simp only [inner_add_right,real_inner_smul_right]
    convert he using 1 <;> dsimp [a,b] <;> ring
  simp only [SolidGeom.CapPolar.caps,Set.mem_setOf_eq,SolidGeom.CapPolar.polar_norm P.e P.frame,
    true_and,hcap]
  constructor
  · intro h
    exact h (SolidGeom.CapPolar.winner P φ)
  · intro h j
    exact h.trans (SolidGeom.CapPolar.winner_min P φ j)

private lemma SolidGeom.CapPolar.caps_measurable (P : Profile) : MeasurableSet (SolidGeom.CapPolar.caps P) := by
  have hc : IsClosed (SolidGeom.CapPolar.caps P) := by
    have he : SolidGeom.CapPolar.caps P = {u : E3 | ‖u‖=1} ∩ ⋂ j, {u | P.height j ≤ inner ℝ (P.normal j) u} := by
      ext u
      simp [SolidGeom.CapPolar.caps]
    rw [he]
    exact (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop))
  exact hc.measurableSet

private lemma SolidGeom.CapPolar.winner_measurable (P : Profile) : Measurable (SolidGeom.CapPolar.winner P) := by
  unfold SolidGeom.CapPolar.winner
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · exact (measurableSet_le (P.rho_continuous 0).measurable (P.rho_continuous 1).measurable).inter
      (measurableSet_le (P.rho_continuous 0).measurable (P.rho_continuous 2).measurable)
  · exact measurableSet_le (P.rho_continuous 1).measurable (P.rho_continuous 2).measurable

private lemma SolidGeom.CapPolar.sector_measurable (P : Profile) (j : Fin 3) :
    MeasurableSet (SolidGeom.CapPolar.sector P j) :=
  measurableSet_Icc.inter ((SolidGeom.CapPolar.winner_measurable P)
    (MeasurableSet.singleton j))

#print axioms SolidGeom.CapPolar.ray_membership

private lemma SolidGeom.CapPolar.dOmega_finite : IsFiniteMeasure dOmega := by
  dsimp [dOmega,sphereMeasure]
  infer_instance

private lemma SolidGeom.CapPolar.profile_radius_range (P : Profile) (φ : ℝ) :
    0 ≤ SolidGeom.CapPolar.radius P φ ∧ SolidGeom.CapPolar.radius P φ ≤ Real.pi :=
  ⟨(P.rho_range _ φ).1.le,(P.rho_range _ φ).2.le⟩

private lemma SolidGeom.CapPolar.polar_swap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (P : Profile) (f : E3 → F)
    (hf : StronglyMeasurable f) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ u, ‖f u‖ ≤ M) :
    (∫ u, f u ∂dOmega) =
      ∫ φ in Set.Icc 0 (2*Real.pi), ∫ t in (0)..Real.pi,
        Real.sin t • f (SolidGeom.CapPolar.polar P.e t φ) := by
  letI : IsFiniteMeasure dOmega := SolidGeom.CapPolar.dOmega_finite
  have hfI : Integrable f dOmega :=
    (integrable_const M).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [SphereGeom.integral_dOmega_frame P.e P.frame f hfI]
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 Real.pi)
  let ν : Measure ℝ := volume.restrict (Set.Icc 0 (2*Real.pi))
  letI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  letI : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  let H : ℝ × ℝ → F := fun z => Real.sin z.1 • f (SolidGeom.CapPolar.polar P.e z.1 z.2)
  have hpol : Continuous (fun z : ℝ × ℝ => SolidGeom.CapPolar.polar P.e z.1 z.2) := by
    unfold SolidGeom.CapPolar.polar
    fun_prop
  have hH : StronglyMeasurable H :=
    (Real.continuous_sin.comp continuous_fst).stronglyMeasurable.smul (hf.comp_measurable hpol.measurable)
  have hHI : Integrable H (μ.prod ν) := by
    apply (integrable_const M).mono' hH.aestronglyMeasurable
    filter_upwards with z
    change ‖Real.sin z.1 • f (SolidGeom.CapPolar.polar P.e z.1 z.2)‖ ≤ M
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ 1*M := mul_le_mul (Real.abs_sin_le_one _) (hbound _) (norm_nonneg _) (by norm_num)
      _ = M := one_mul M
  have hs := MeasureTheory.integral_integral_swap
    (f := fun t φ => Real.sin t • f (SolidGeom.CapPolar.polar P.e t φ))
    (show Integrable (Function.uncurry (fun t φ => Real.sin t • f (SolidGeom.CapPolar.polar P.e t φ))) (μ.prod ν) from hHI)
  simp_rw [intervalIntegral.integral_of_le Real.pi_pos.le,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi),
    ← integral_Icc_eq_integral_Ioc]
  exact hs

private lemma SolidGeom.CapPolar.area_indicator_bound (P : Profile) (u : E3) :
    ‖(SolidGeom.CapPolar.caps P).indicator (fun _ : E3 => (1:ℝ)) u‖ ≤ 1 := by
  by_cases hu : u ∈ SolidGeom.CapPolar.caps P <;> simp [hu]

private lemma SolidGeom.CapPolar.moment_indicator_bound (P : Profile) (u : E3) :
    ‖(SolidGeom.CapPolar.caps P).indicator (fun u : E3 => u) u‖ ≤ 1 := by
  by_cases hu : u ∈ SolidGeom.CapPolar.caps P
  · simpa only [Set.indicator_of_mem hu] using hu.1.le
  · simp [hu]

private lemma SolidGeom.CapPolar.area_inner_integral (P : Profile) (φ : ℝ) :
    (∫ t in (0)..Real.pi, Real.sin t *
      (SolidGeom.CapPolar.caps P).indicator (fun _ : E3 => (1:ℝ))
        (SolidGeom.CapPolar.polar P.e t φ)) = 1-Real.cos (SolidGeom.CapPolar.radius P φ) := by
  have he : (∫ t in (0)..Real.pi, Real.sin t *
      (SolidGeom.CapPolar.caps P).indicator (fun _ : E3 => (1:ℝ))
        (SolidGeom.CapPolar.polar P.e t φ)) =
      ∫ t in (0)..Real.pi, ({t : ℝ | t ≤ SolidGeom.CapPolar.radius P φ}).indicator Real.sin t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc 0 Real.pi := by simpa only [Set.uIcc_of_le Real.pi_pos.le] using ht
    have hmem := SolidGeom.CapPolar.ray_membership P t φ ht'
    by_cases hle : t ≤ SolidGeom.CapPolar.radius P φ
    · have hp := hmem.mpr hle
      simp [hp,hle]
    · have hn : SolidGeom.CapPolar.polar P.e t φ ∉ SolidGeom.CapPolar.caps P := fun h => hle (hmem.mp h)
      simp [hn,hle]
  rw [he,intervalIntegral.integral_indicator (SolidGeom.CapPolar.profile_radius_range P φ)]
  rw [integral_sin]
  simp

private lemma SolidGeom.CapPolar.moment_primitive (P : Profile) (φ t : ℝ) :
    HasDerivAt (fun t : ℝ =>
      ((t-Real.sin t*Real.cos t)/2) • SolidGeom.CapPolar.tangent P φ+
      ((Real.sin t)^2/2) • P.e 2)
      (Real.sin t • SolidGeom.CapPolar.polar P.e t φ) t := by
  have h1 := (((hasDerivAt_id t).sub ((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t))).div_const 2).smul_const
    (SolidGeom.CapPolar.tangent P φ)
  have h2 := (((Real.hasDerivAt_sin t).pow 2).div_const 2).smul_const (P.e 2)
  have hd := h1.add h2
  have hscalar : (1-(Real.cos t*Real.cos t+Real.sin t*(-Real.sin t)))/2 = (Real.sin t)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hcoef : ((2:ℝ)*Real.sin t^(2-1)*Real.cos t)/2 = Real.sin t*Real.cos t := by norm_num;ring
  have hvec : ((Real.sin t)^2) • SolidGeom.CapPolar.tangent P φ+
      (Real.sin t*Real.cos t) • P.e 2 = Real.sin t • SolidGeom.CapPolar.polar P.e t φ := by
    unfold SolidGeom.CapPolar.tangent SolidGeom.CapPolar.polar
    module
  change HasDerivAt (fun s : ℝ => ((s-Real.sin s*Real.cos s)/2) • SolidGeom.CapPolar.tangent P φ+
    ((Real.sin s)^2/2) • P.e 2)
    (((1-(Real.cos t*Real.cos t+Real.sin t*(-Real.sin t)))/2) • SolidGeom.CapPolar.tangent P φ+
      (((2:ℝ)*Real.sin t^(2-1)*Real.cos t)/2) • P.e 2) t at hd
  rwa [hscalar,hcoef,hvec] at hd

private lemma SolidGeom.CapPolar.moment_inner_integral (P : Profile) (φ : ℝ) :
    (∫ t in (0)..Real.pi, Real.sin t •
      (SolidGeom.CapPolar.caps P).indicator (fun u : E3 => u)
        (SolidGeom.CapPolar.polar P.e t φ)) =
      SolidGeom.CapPolar.momentDensity P (SolidGeom.CapPolar.winner P φ) φ := by
  have he : (∫ t in (0)..Real.pi, Real.sin t •
      (SolidGeom.CapPolar.caps P).indicator (fun u : E3 => u)
        (SolidGeom.CapPolar.polar P.e t φ)) =
      ∫ t in (0)..Real.pi, ({t : ℝ | t ≤ SolidGeom.CapPolar.radius P φ}).indicator
        (fun t => Real.sin t • SolidGeom.CapPolar.polar P.e t φ) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc 0 Real.pi := by simpa only [Set.uIcc_of_le Real.pi_pos.le] using ht
    have hmem := SolidGeom.CapPolar.ray_membership P t φ ht'
    by_cases hle : t ≤ SolidGeom.CapPolar.radius P φ
    · have hp := hmem.mpr hle
      simp [hp,hle]
    · have hn : SolidGeom.CapPolar.polar P.e t φ ∉ SolidGeom.CapPolar.caps P := fun h => hle (hmem.mp h)
      simp [hn,hle]
  rw [he,intervalIntegral.integral_indicator (SolidGeom.CapPolar.profile_radius_range P φ)]
  have hc : Continuous (fun t => Real.sin t • SolidGeom.CapPolar.polar P.e t φ) := by
    unfold SolidGeom.CapPolar.polar
    fun_prop
  have hi : IntervalIntegrable (fun t => Real.sin t • SolidGeom.CapPolar.polar P.e t φ) volume 0
      (SolidGeom.CapPolar.radius P φ) := hc.intervalIntegrable _ _
  have hs := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => SolidGeom.CapPolar.moment_primitive P φ t) hi
  simpa only [Real.sin_zero,Real.cos_zero,mul_zero,zero_mul,sub_zero,zero_sub,zero_div,
    zero_pow (by decide : (2:ℕ) ≠ 0),zero_smul,add_zero,sub_zero,
    SolidGeom.CapPolar.momentDensity,SolidGeom.CapPolar.radius] using hs

private lemma SolidGeom.CapPolar.sum_sectors {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (P : Profile) (q : Fin 3 → ℝ → F)
    (hq : ∀ j, Continuous (q j)) :
    (∫ φ in Set.Icc 0 (2*Real.pi), q (SolidGeom.CapPolar.winner P φ) φ) =
      ∑ j : Fin 3, ∫ φ in SolidGeom.CapPolar.sector P j, q j φ := by
  let A : Fin 3 → Set ℝ := fun j => {φ | SolidGeom.CapPolar.winner P φ = j}
  have hA : ∀ j, MeasurableSet (A j) := fun j =>
    (SolidGeom.CapPolar.winner_measurable P) (MeasurableSet.singleton j)
  have hpoint : ∀ φ, q (SolidGeom.CapPolar.winner P φ) φ =
      ∑ j : Fin 3, (A j).indicator (q j) φ := by
    intro φ
    have hs : ∑ j : Fin 3, (A j).indicator (q j) φ = q (SolidGeom.CapPolar.winner P φ) φ := by
      calc
        _ = (A (SolidGeom.CapPolar.winner P φ)).indicator (q (SolidGeom.CapPolar.winner P φ)) φ := by
          apply Finset.sum_eq_single (SolidGeom.CapPolar.winner P φ)
          · intro j hj hne
            have hn : φ ∉ A j := by exact fun h => hne h.symm
            simp [hn]
          · simp
        _ = _ := by simp [A]
    exact hs.symm
  simp_rw [hpoint]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_indicator (hA j),Measure.restrict_restrict (hA j)]
    congr 1
    simp only [SolidGeom.CapPolar.sector,A,Set.inter_comm]
  · intro j hj
    exact ((hq j).integrableOn_Icc).indicator (hA j)

#print axioms SolidGeom.CapPolar.polar_swap
#print axioms SolidGeom.CapPolar.area_inner_integral
#print axioms SolidGeom.CapPolar.moment_inner_integral

theorem proof_SolidGeom_CapPolar_area_eq_polar_sectors (P : Profile) :
    (dOmega (SolidGeom.CapPolar.caps P)).toReal =
      ∑ j : Fin 3, ∫ φ in SolidGeom.CapPolar.sector P j, (1-Real.cos (P.rho j φ)) := by
  letI : IsFiniteMeasure dOmega := SolidGeom.CapPolar.dOmega_finite
  have hm := SolidGeom.CapPolar.caps_measurable P
  have hs := SolidGeom.CapPolar.polar_swap P
    ((SolidGeom.CapPolar.caps P).indicator (fun _ : E3 => (1:ℝ)))
    (stronglyMeasurable_const.indicator hm) 1 (by norm_num)
    (SolidGeom.CapPolar.area_indicator_bound P)
  rw [integral_indicator hm] at hs
  have harea : (∫ u in SolidGeom.CapPolar.caps P, (1:ℝ) ∂dOmega) =
      (dOmega (SolidGeom.CapPolar.caps P)).toReal := by simp [Measure.real]
  rw [harea] at hs
  simp only [smul_eq_mul,SolidGeom.CapPolar.area_inner_integral] at hs
  rw [hs]
  have hcont : ∀ j : Fin 3, Continuous (fun φ => 1-Real.cos (P.rho j φ)) := by
    intro j
    exact continuous_const.sub (Real.continuous_cos.comp (P.rho_continuous j))
  exact SolidGeom.CapPolar.sum_sectors P (fun j φ => 1-Real.cos (P.rho j φ)) hcont

#print axioms proof_SolidGeom_CapPolar_area_eq_polar_sectors
