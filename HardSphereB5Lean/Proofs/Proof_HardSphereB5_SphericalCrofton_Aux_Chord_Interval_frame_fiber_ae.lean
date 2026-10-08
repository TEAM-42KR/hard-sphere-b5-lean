import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_chordLen_le_pi_ae
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_density_measurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_frame_double_pullback
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_finite_or_short_arc
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_single_arc_transport
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 1000000
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_frame_fiber_ae {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern) (F₁ F₂ : Pt → Pt) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂) (hF : ∀ p, ‖p‖ = 1 → Orthonormal ℝ ![F₁ p, F₂ p, p]) : ∀ᵐ p ∂dOmega, (∫⁻ t₁ in Set.Ioc 0 (2 * π), ∫⁻ t₂ in Set.Ioc 0 (2 * π), (fun u v : Pt => if u ∈ K ∧ v ∈ K ∧ (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0) (Real.cos t₁ • F₁ p + Real.sin t₁ • F₂ p) (Real.cos t₂ • F₁ p + Real.sin t₂ • F₂ p) * ENNReal.ofReal |Real.sin (t₁ - t₂)|) = ENNReal.ofReal ((fun G => if 0 < chordLen K G then kK f (chordLen K G) else 0) (greatCircle p))  := by
  let g : Pt → Pt → ENNReal := fun u v =>
    if u ∈ K ∧ v ∈ K ∧ (1 / 2 : ℝ) ≤ inner ℝ u v
      then ENNReal.ofReal (wK f (inner ℝ u v)) else 0
  let H0 : Pt → Pt → ENNReal := fun u v =>
    (if (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0) *
      ENNReal.ofReal (Real.sqrt (1 - (inner ℝ u v) ^ 2))
  let H : Pt → Pt → ENNReal := fun u v =>
    g u v * ENNReal.ofReal (Real.sqrt (1 - (inner ℝ u v) ^ 2))
  have hg : Measurable (Function.uncurry g) :=
    HardSphereB5.SphericalCrofton.Aux.Chord.Pair.density_measurable K hK.isCompact.measurableSet f
  have hH : Measurable (Function.uncurry H) :=
    hg.mul (ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      (measurable_const.sub ((measurable_fst.inner measurable_snd).pow_const 2))))
  have hHpoint (u v : Pt) : H u v =
      K.indicator (fun u => K.indicator (fun v => H0 u v) v) u := by
    by_cases hu : u ∈ K <;> by_cases hv : v ∈ K <;>
      simp [H, H0, g, Set.indicator, hu, hv]
  have hunit : ∀ᵐ p ∂dOmega, ‖p‖ = 1 := by
    have hs : ∀ᵐ p ∂dOmega, p ∈ Metric.sphere (0 : Pt) 1 :=
      ae_iff.mpr SphereGeom.dOmega_compl_sphere
    filter_upwards [hs] with p hp
    simpa [Metric.mem_sphere, dist_zero_right] using hp
  letI : NullSingletonClass arcMeasure :=
    MeasureTheory.Measure.nullSingletonClass_hausdorff Pt (by norm_num : (0 : ℝ) < 1)
  have hk0 : kK f 0 = 0 := by
    simp [kK, min_eq_left (by positivity : (0 : ℝ) ≤ π / 3)]
  filter_upwards [hunit, HardSphereB5.SphericalCrofton.Aux.Chord.chordLen_le_pi_ae hK] with p hpn hL
  have hE := hF p hpn
  let E1 := F₁ p
  let E2 := F₂ p
  let C : ℝ → Pt := circlePt 0 E1 E2 1
  let S : Set Pt := greatCircle p ∩ K
  have h00 : inner ℝ E1 E1 = 1 := by simpa [E1,E2] using (orthonormal_iff_ite.mp hE (0 : Fin 3) 0)
  have h01 : inner ℝ E1 E2 = 0 := by simpa [E1,E2] using (orthonormal_iff_ite.mp hE (0 : Fin 3) 1)
  have h10 : inner ℝ E2 E1 = 0 := by simpa [E1,E2] using (orthonormal_iff_ite.mp hE (1 : Fin 3) 0)
  have h11 : inner ℝ E2 E2 = 1 := by simpa [E1,E2] using (orthonormal_iff_ite.mp hE (1 : Fin 3) 1)
  have hCt (t : ℝ) : C t = Real.cos t • F₁ p + Real.sin t • F₂ p := by
    simp [C, circlePt, E1, E2]
  have hinner (s t : ℝ) : inner ℝ (C s) (C t) = Real.cos (s - t) := by
    simp only [C, circlePt, zero_add, one_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, h00, h01, h10, h11,
      mul_one, mul_zero, zero_mul, add_zero, zero_add]
    rw [Real.cos_sub]
    ring
  have hsqrt (s t : ℝ) : Real.sqrt (1 - (inner ℝ (C s) (C t)) ^ 2) =
      |Real.sin (s - t)| := by
    rw [hinner, show 1 - Real.cos (s - t) ^ 2 = Real.sin (s - t) ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq (s - t)]]
    exact Real.sqrt_sq_eq_abs _
  simp_rw [← hCt]
  change (∫⁻ s in Set.Ioc 0 (2 * π), ∫⁻ t in Set.Ioc 0 (2 * π),
      g (C s) (C t) * ENNReal.ofReal |Real.sin (s - t)|) =
    ENNReal.ofReal (if 0 < chordLen K (greatCircle p) then kK f (chordLen K (greatCircle p)) else 0)
  have hfiber : (∫⁻ s in Set.Ioc 0 (2 * π), ∫⁻ t in Set.Ioc 0 (2 * π),
      g (C s) (C t) * ENNReal.ofReal |Real.sin (s - t)|) =
      ∫⁻ u in greatCircle p, ∫⁻ v in greatCircle p, H u v ∂arcMeasure ∂arcMeasure := by
    calc
      _ = ∫⁻ s in Set.Ioc 0 (2 * π), ∫⁻ t in Set.Ioc 0 (2 * π), H (C s) (C t) := by
        apply lintegral_congr
        intro s
        apply lintegral_congr
        intro t
        dsimp [H]
        rw [hsqrt]
      _ = _ := HardSphereB5.SphericalCrofton.Aux.Chord.Interval.frame_double_pullback E1 E2 p hE H hH
  have hin (u : Pt) : (∫⁻ v in greatCircle p, H u v ∂arcMeasure) =
      K.indicator (fun u => ∫⁻ v in S, H0 u v ∂arcMeasure) u := by
    by_cases hu : u ∈ K
    · simp only [hHpoint, Set.indicator_of_mem hu]
      rw [setLIntegral_indicator hK.isCompact.measurableSet, Set.inter_comm K (greatCircle p)]
    · simp [hHpoint, Set.indicator, hu]
  have hdouble : (∫⁻ u in greatCircle p, ∫⁻ v in greatCircle p,
      H u v ∂arcMeasure ∂arcMeasure) =
      ∫⁻ u in S, ∫⁻ v in S, H0 u v ∂arcMeasure ∂arcMeasure := by
    simp_rw [hin]
    rw [setLIntegral_indicator hK.isCompact.measurableSet, Set.inter_comm K (greatCircle p)]
  rw [hfiber, hdouble]
  rcases HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_finite_or_short_arc hK E1 E2 p hE hL with hf | ha
  · have hnull : arcMeasure S = 0 := hf.measure_zero arcMeasure
    have hr0 : arcMeasure.restrict S = 0 := Measure.restrict_eq_zero.mpr hnull
    have hlen : chordLen K (greatCircle p) = 0 := by
      change (arcMeasure S).toReal = 0
      rw [hnull]
      rfl
    simp [hr0, hlen]
  · obtain ⟨a,b,hab,hπ,hgeom⟩ := ha
    obtain ⟨hval,hlen⟩ := HardSphereB5.SphericalCrofton.Aux.Chord.Interval.single_arc_transport f E1 E2 p hE a b hab hπ hgeom
    change (∫⁻ u in S, ∫⁻ v in S, H0 u v ∂arcMeasure ∂arcMeasure) = ENNReal.ofReal (kK f (b - a)) at hval
    rw [hval]
    by_cases hp : 0 < chordLen K (greatCircle p)
    · rw [if_pos hp, hlen]
    · have hz : b - a = 0 := by
        rw [hlen] at hp
        linarith
      simp only [if_neg hp, hz, hk0]
