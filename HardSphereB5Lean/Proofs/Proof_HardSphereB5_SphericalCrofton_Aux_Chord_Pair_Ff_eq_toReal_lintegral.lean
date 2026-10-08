import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_density_measurable
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_Ff_eq_toReal_lintegral {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern) : Ff f K = (∫⁻ u, ∫⁻ v, (fun u v : Pt => if u ∈ K ∧ v ∈ K ∧ (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0) u v ∂dOmega ∂dOmega).toReal := by
  letI : IsFiniteMeasure dOmega := by
    dsimp [dOmega, sphereMeasure]
    infer_instance
  let g : Pt → Pt → ENNReal := (fun u v : Pt => if u ∈ K ∧ v ∈ K ∧ (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0)
  have hg : Measurable (Function.uncurry g) :=
    HardSphereB5.SphericalCrofton.Aux.Chord.Pair.density_measurable K hK.isCompact.measurableSet f
  have hw (x : ℝ) (hx : (1 / 2 : ℝ) ≤ x) : 0 ≤ wK f x := by
    cases f <;> simp only [wK]
    · positivity
    · linarith
  have hbound (u v : Pt) : g u v ≤ 1 := by
    dsimp [g]
    split_ifs with hh
    · have hu : ‖u‖ = 1 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hK.subset_sphere hh.1
      have hv : ‖v‖ = 1 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hK.subset_sphere hh.2.1
      have hc : inner ℝ u v ≤ 1 := by simpa [hu, hv] using real_inner_le_norm u v
      have hwle : wK f (inner ℝ u v) ≤ 1 := by cases f <;> simp_all [wK]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hwle
    · simp
  have hfin (u : Pt) : (∫⁻ v, g u v ∂dOmega) < ⊤ := by
    have hh := lintegral_mono (μ := dOmega) (hbound u)
    exact lt_of_le_of_lt hh (by simpa using (measure_lt_top dOmega Set.univ))
  have hpoint (u v : Pt) : (g u v).toReal =
      K.indicator (fun u => K.indicator
        (fun v => wK f (inner ℝ u v) * (if (1 / 2 : ℝ) ≤ inner ℝ u v then 1 else 0)) v) u := by
    by_cases hu : u ∈ K <;> by_cases hv : v ∈ K <;>
      simp [g, Set.indicator, hu, hv]
    split_ifs with hc
    · have hc' : (1 / 2 : ℝ) ≤ inner ℝ u v := by simpa only [one_div] using hc
      simp [ENNReal.toReal_ofReal (hw _ hc')]
    · simp
  have hin : (∫ u, ∫ v, (g u v).toReal ∂dOmega ∂dOmega) = Ff f K := by
    simp_rw [hpoint]
    rw [integral_integral_indicator _ hK.isCompact.measurableSet]
    simp_rw [integral_indicator hK.isCompact.measurableSet]
    rfl
  rw [← hin]
  have hi (u : Pt) : (∫ v, (g u v).toReal ∂dOmega) = (∫⁻ v, g u v ∂dOmega).toReal :=
    integral_toReal (hg.of_uncurry_left.aemeasurable)
      (Filter.Eventually.of_forall (fun v => lt_of_le_of_lt (hbound u v) (by simp)))
  simp_rw [hi]
  exact integral_toReal hg.lintegral_prod_right.aemeasurable (Filter.Eventually.of_forall hfin)
