import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_integral_dOmega_frame
set_option autoImplicit false
open MeasureTheory Real SphereGeom

private theorem g3m_transverse_frame (e : Fin 3 → E3) (he : Orthonormal ℝ e) (h k l b : ℝ) :
 inner ℝ (e 0) (∫ u in cap (e 2) h ∩ cap (k • e 2 + l • e 0) b, u ∂dOmega) =
 ∫ θ in (0:ℝ)..Real.pi, ∫ φ in (0:ℝ)..(2*Real.pi),
  Real.sin θ * (if h ≤ Real.cos θ ∧ b ≤ k*Real.cos θ + l*Real.sin θ*Real.cos φ then
   Real.sin θ*Real.cos φ else 0) := by
  classical
  let S := cap (e 2) h ∩ cap (k • e 2 + l • e 0) b
  have hcap (v : E3) (d : ℝ) : MeasurableSet (cap v d) := by
    unfold cap
    exact ((isClosed_eq (continuous_norm : Continuous (fun u : E3 => ‖u‖))
      (continuous_const : Continuous (fun _ : E3 => (1:ℝ)))).inter
      (isClosed_le (continuous_const : Continuous (fun _ : E3 => d))
        (by fun_prop : Continuous (fun u : E3 => inner ℝ v u)))).measurableSet
  have hs : MeasurableSet S := (hcap _ _).inter (hcap _ _)
  haveI : IsFiniteMeasure dOmega := by unfold dOmega sphereMeasure; infer_instance
  have hfi : Integrable (S.indicator (fun u : E3 => u)) dOmega := by
    refine (integrable_const (1:ℝ)).mono' ?_ ?_
    · exact (measurable_id.indicator hs).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => by
        by_cases hu : u ∈ S
        · rw [Set.indicator_of_mem hu]
          exact le_of_eq hu.1.1
        · simp [Set.indicator_of_notMem hu]
  rw [← integral_indicator hs]
  rw [← integral_inner hfi (e 0)]
  rw [SphereGeom.integral_dOmega_frame e he _ (hfi.const_inner (e 0))]
  apply intervalIntegral.integral_congr
  intro θ hθ
  apply intervalIntegral.integral_congr
  intro φ hφ
  dsimp only
  change sin θ * _ = sin θ * _
  apply congrArg (fun x : ℝ => sin θ * x)
  let u := (sin θ*cos φ) • e 0 + (sin θ*sin φ) • e 1 + cos θ • e 2
  have hei := orthonormal_iff_ite.mp he
  have hnorm : ‖u‖=1 := by
    have hh : inner ℝ u u = 1 := by
      dsimp [u]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hei]
      norm_num [Fin.ext_iff]
      nlinarith [sin_sq_add_cos_sq θ, congrArg (fun x : ℝ => sin θ ^ 2*x) (sin_sq_add_cos_sq φ)]
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg u]
  have h0 : inner ℝ (e 0) u = sin θ*cos φ := by
    dsimp [u]; simp only [inner_add_right, real_inner_smul_right, hei]; norm_num [Fin.ext_iff]
  have h2 : inner ℝ (e 2) u = cos θ := by
    dsimp [u]; simp only [inner_add_right, real_inner_smul_right, hei]; norm_num [Fin.ext_iff]
  have hw : inner ℝ (k • e 2 + l • e 0) u = k*cos θ+l*sin θ*cos φ := by
    simp only [inner_add_left, real_inner_smul_left, h0, h2]
    ring
  change inner ℝ (e 0) (S.indicator (fun v : E3 => v) u) = _
  have hm : u ∈ S ↔ h ≤ cos θ ∧ b ≤ k*cos θ+l*sin θ*cos φ := by
    simp [S, cap, hnorm, h2, hw]
  by_cases hh : h ≤ cos θ ∧ b ≤ k*cos θ+l*sin θ*cos φ
  · rw [Set.indicator_of_mem (hm.mpr hh), if_pos hh, h0]
  · rw [Set.indicator_of_notMem (mt hm.mp hh), if_neg hh]
    simp

open MeasureTheory Real SphereGeom
set_option maxHeartbeats 1200000

private theorem clipped_cos_integral (q : ℝ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi),
      (if q ≤ Real.cos φ then Real.cos φ else 0)) =
      2 * Real.sqrt (1 - q ^ 2) := by
  classical
  let f : ℝ → ℝ := fun x => if q ≤ Real.cos x then Real.cos x else 0
  change (∫ x in (0 : ℝ)..(2 * Real.pi), f x) = _
  by_cases hlow : q ≤ -1
  · have hf : f = Real.cos := by
      funext x
      exact if_pos (hlow.trans (Real.neg_one_le_cos x))
    have hs : Real.sqrt (1 - q ^ 2) = 0 := by
      apply Real.sqrt_eq_zero_of_nonpos
      nlinarith
    rw [hf, integral_cos, Real.sin_two_pi, Real.sin_zero, hs]
    ring
  by_cases hhigh : 1 < q
  · have hf : f = fun _ => (0 : ℝ) := by
      funext x
      exact if_neg (not_le_of_gt ((Real.cos_le_one x).trans_lt hhigh))
    have hs : Real.sqrt (1 - q ^ 2) = 0 := by
      apply Real.sqrt_eq_zero_of_nonpos
      nlinarith
    rw [hf, hs]
    simp
  have hqlo : -1 ≤ q := le_of_lt (lt_of_not_ge hlow)
  have hqhi : q ≤ 1 := le_of_not_gt hhigh
  have hfm : Measurable f := by
    exact Measurable.piecewise
      (measurableSet_le measurable_const Real.continuous_cos.measurable)
      Real.continuous_cos.measurable measurable_const
  have hint (a b : ℝ) : IntervalIntegrable f volume a b := by
    apply (intervalIntegral.intervalIntegrable_cos : IntervalIntegrable Real.cos volume a b).mono_fun
      hfm.aestronglyMeasurable
    filter_upwards [] with x
    dsimp [f]
    split_ifs <;> simp
  have hsymf : (fun x => f (2 * Real.pi - x)) = f := by
    funext x
    dsimp [f]
    rw [Real.cos_two_pi_sub]
  have hsym : (∫ x in Real.pi..(2 * Real.pi), f x) =
      ∫ x in (0 : ℝ)..Real.pi, f x := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := Real.pi) f (2 * Real.pi)
    rw [hsymf, show 2 * Real.pi - Real.pi = Real.pi by ring, sub_zero] at h
    exact h.symm
  have htwice : (∫ x in (0 : ℝ)..(2 * Real.pi), f x) =
      2 * (∫ x in (0 : ℝ)..Real.pi, f x) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint 0 Real.pi) (hint Real.pi (2 * Real.pi)), hsym]
    ring
  let A := Real.arccos q
  have hA0 : 0 ≤ A := Real.arccos_nonneg q
  have hApi : A ≤ Real.pi := Real.arccos_le_pi q
  have hcos : Real.cos A = q := Real.cos_arccos hqlo hqhi
  have hleft : (∫ x in (0 : ℝ)..A, f x) = ∫ x in (0 : ℝ)..A, Real.cos x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hA0
    intro x hx
    dsimp only [f]
    apply if_pos
    rw [← hcos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hx.1.le hApi hx.2.le
  have hright : (∫ x in A..Real.pi, f x) = 0 := by
    calc
      (∫ x in A..Real.pi, f x) = ∫ _ in A..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hApi
        intro x hx
        dsimp only [f]
        apply if_neg
        have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hA0 hx.2.le hx.1
        rw [hcos] at hh
        exact not_le_of_gt hh
      _ = 0 := by simp
  rw [htwice, ← intervalIntegral.integral_add_adjacent_intervals
    (hint 0 A) (hint A Real.pi), hleft, hright, add_zero, integral_cos, Real.sin_zero,
    sub_zero]
  exact congrArg (fun x : ℝ => 2 * x) (Real.sin_arccos q)

private theorem g3m_transverse_slices (h k l b : ℝ) (hh0 : -1 ≤ h) (hh1 : h ≤ 1) (hl : 0 < l) :
    (∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Real.sin θ * (if h ≤ Real.cos θ ∧
        b ≤ k * Real.cos θ + l * Real.sin θ * Real.cos φ
        then Real.sin θ * Real.cos φ else 0)) =
    (2 / l) * (∫ t in h..1,
      Real.sqrt (l ^ 2 * (1 - t ^ 2) - (b - k * t) ^ 2)) := by
  classical
  let G : ℝ → ℝ := fun t => Real.sqrt (l ^ 2 * (1 - t ^ 2) - (b - k * t) ^ 2)
  let F : ℝ → ℝ := fun x => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Real.sin x * (if h ≤ Real.cos x ∧
        b ≤ k * Real.cos x + l * Real.sin x * Real.cos φ
        then Real.sin x * Real.cos φ else 0)
  let g : ℝ → ℝ := fun x => (2 / l) * (Real.sin x * G (Real.cos x))
  have hGc : Continuous G := by dsimp [G]; fun_prop
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have angular (x : ℝ) (hx0 : 0 < x) (hxpi : x < Real.pi)
      (hc : h ≤ Real.cos x) : F x = g x := by
    have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
    let s : ℝ := l * Real.sin x
    let D : ℝ := b - k * Real.cos x
    let q : ℝ := D / s
    have hs : 0 < s := mul_pos hl hsin
    have hcond (φ : ℝ) : (h ≤ Real.cos x ∧
        b ≤ k * Real.cos x + l * Real.sin x * Real.cos φ) ↔ q ≤ Real.cos φ := by
      rw [and_iff_right hc]
      dsimp only [q]
      rw [div_le_iff₀ hs]
      dsimp only [s, D]
      constructor <;> intro hb <;> nlinarith
    have htrig : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    have hp : l ^ 2 * (1 - Real.cos x ^ 2) - (b - k * Real.cos x) ^ 2 =
        s ^ 2 * (1 - q ^ 2) := by
      rw [← htrig]
      dsimp only [q]
      field_simp [ne_of_gt hs]
      <;> dsimp only [s, D]
      <;> ring
    have hrad : G (Real.cos x) = s * Real.sqrt (1 - q ^ 2) := by
      dsimp only [G]
      rw [hp, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
    calc
      F x = Real.sin x ^ 2 * (∫ φ in (0 : ℝ)..(2 * Real.pi),
          (if q ≤ Real.cos φ then Real.cos φ else 0)) := by
        dsimp only [F]
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro φ _
        dsimp only
        simp only [hcond φ]
        split_ifs <;> ring
      _ = Real.sin x ^ 2 * (2 * Real.sqrt (1 - q ^ 2)) := by
        rw [clipped_cos_integral]
      _ = g x := by
        dsimp only [g]
        rw [hrad]
        dsimp only [s]
        field_simp [ne_of_gt hl]
        <;> ring
  let A := Real.arccos h
  have hA0 : 0 ≤ A := Real.arccos_nonneg h
  have hApi : A ≤ Real.pi := Real.arccos_le_pi h
  have hcos : Real.cos A = h := Real.cos_arccos hh0 hh1
  have hleft (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) A) : F x = g x := by
    apply angular x hx.1 (hx.2.trans_le hApi)
    rw [← hcos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hx.1.le hApi hx.2.le
  have hright (x : ℝ) (hx : x ∈ Set.Ioo A Real.pi) : F x = 0 := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hA0 hx.2.le hx.1
    rw [hcos] at hh
    simp [F, not_le_of_gt hh]
  have hIl : IntervalIntegrable F volume 0 A := by
    apply (hgc.intervalIntegrable 0 A).congr_uIoo
    rw [Set.uIoo_of_le hA0]
    intro x hx
    exact (hleft x hx).symm
  have hIr : IntervalIntegrable F volume A Real.pi := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume A Real.pi).congr_uIoo
    rw [Set.uIoo_of_le hApi]
    intro x hx
    exact (hright x hx).symm
  have hEl : (∫ x in (0 : ℝ)..A, F x) = ∫ x in (0 : ℝ)..A, g x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hA0
    exact hleft
  have hEr : (∫ x in A..Real.pi, F x) = 0 := by
    calc
      (∫ x in A..Real.pi, F x) = ∫ _ in A..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hApi
        exact hright
      _ = 0 := by simp
  have hsub : (∫ x in (0 : ℝ)..A, Real.sin x * G (Real.cos x)) =
      ∫ t in h..1, G t := by
    have hs := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := A) (f := Real.cos)
      (f' := fun x => -Real.sin x) (g := G)
      (fun x _ => Real.hasDerivAt_cos x) Real.continuous_sin.neg.continuousOn hGc
    simp only [Function.comp_apply, Real.cos_zero, hcos] at hs
    calc
      (∫ x in (0 : ℝ)..A, Real.sin x * G (Real.cos x)) =
          -(∫ x in (0 : ℝ)..A, G (Real.cos x) * (-Real.sin x)) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = -(∫ t in (1 : ℝ)..h, G t) := congrArg Neg.neg hs
      _ = ∫ t in h..1, G t := by rw [intervalIntegral.integral_symm]; simp
  change (∫ x in (0 : ℝ)..Real.pi, F x) = (2 / l) * (∫ t in h..1, G t)
  rw [← intervalIntegral.integral_add_adjacent_intervals hIl hIr, hEl, hEr, add_zero]
  dsimp only [g]
  rw [intervalIntegral.integral_const_mul, hsub]

theorem proof_SphereGeom_cap_moment_transverse (e : Fin 3 → E3) (he : Orthonormal ℝ e) (h k l b : ℝ) (hh0 : -1 ≤ h) (hh1 : h ≤ 1) (hl : 0 < l) :
 inner ℝ (e 0) (∫ u in cap (e 2) h ∩ cap (k • e 2 + l • e 0) b, u ∂dOmega) = (2 / l) * (∫ t in h..1, Real.sqrt (l ^ 2 * (1 - t ^ 2) - (b - k * t) ^ 2)) := by
  rw [g3m_transverse_frame e he h k l b]
  exact g3m_transverse_slices h k l b hh0 hh1 hl
