import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_square_difference_weight
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_even_overlap
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_double_interval (f : Kern) (L : ℝ) (h0 : 0 ≤ L) (hπ : L ≤ π) : (∫⁻ s in Set.Ioc 0 L, ∫⁻ t in Set.Ioc 0 L, (if (1 / 2 : ℝ) ≤ Real.cos (s - t) then ENNReal.ofReal (wK f (Real.cos (s - t))) else 0) * ENNReal.ofReal |Real.sin (s - t)|) = ENNReal.ofReal (kK f L) := by
  let h : ℝ → ENNReal := fun r =>
    (if (1 / 2 : ℝ) ≤ Real.cos r then ENNReal.ofReal (wK f (Real.cos r)) else 0) *
      ENNReal.ofReal |Real.sin r|
  have hc : Continuous (fun r : ℝ => wK f (Real.cos r)) := by
    cases f
    · exact continuous_const
    · exact Real.continuous_cos
  have hm : Measurable h :=
    (Measurable.ite (measurableSet_le measurable_const Real.continuous_cos.measurable)
      (ENNReal.measurable_ofReal.comp hc.measurable) measurable_const).mul
      (ENNReal.measurable_ofReal.comp Real.continuous_sin.abs.measurable)
  have he (r : ℝ) : h (-r) = h r := by simp [h, Real.cos_neg, Real.sin_neg, abs_neg]
  have hflip : (∫⁻ s in Set.Ioc 0 L, ∫⁻ t in Set.Ioc 0 L, h (s - t)) =
      ∫⁻ s in Set.Ioc 0 L, ∫⁻ t in Set.Ioc 0 L, h (t - s) := by
    apply lintegral_congr
    intro s
    apply lintegral_congr
    intro t
    simpa only [neg_sub] using he (t - s)
  change (∫⁻ s in Set.Ioc 0 L, ∫⁻ t in Set.Ioc 0 L, h (s - t)) = _
  rw [hflip, HardSphereB5.SphericalCrofton.Aux.Chord.Interval.square_difference_weight h hm L,
    HardSphereB5.SphericalCrofton.Aux.Chord.Interval.even_overlap h he L h0]
  let q : ℝ → ℝ := fun r => (L - r) * wK f (Real.cos r) * Real.sin r
  have hmin : 0 ≤ min L (π / 3) := le_min h0 (by positivity)
  have hcos (r : ℝ) (hr0 : 0 ≤ r) (hrπ : r ≤ π) :
      ((1 / 2 : ℝ) ≤ Real.cos r) ↔ r ≤ π / 3 := by
    rw [← Real.cos_pi_div_three]
    exact Real.strictAntiOn_cos.le_iff_ge
      ⟨by positivity, by linarith [Real.pi_pos]⟩ ⟨hr0, hrπ⟩
  have hnn (r : ℝ) (hr : r ∈ Set.Ioc 0 (min L (π / 3))) : 0 ≤ q r := by
    have hrL : r ≤ L := le_trans hr.2 (min_le_left _ _)
    have hrπ : r ≤ π := le_trans (le_trans hr.2 (min_le_right _ _)) (by linarith [Real.pi_pos])
    have hw : 0 ≤ wK f (Real.cos r) := by
      have hh := (hcos r hr.1.le hrπ).mpr (le_trans hr.2 (min_le_right _ _))
      cases f
      · simp [wK]
      · simpa only [wK] using (show 0 ≤ Real.cos r by linarith)
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hrL) hw)
      (Real.sin_nonneg_of_nonneg_of_le_pi hr.1.le hrπ)
  have hcut : (∫⁻ r in Set.Ioc 0 L, h r * ENNReal.ofReal (L - r)) =
      ∫⁻ r in Set.Ioc 0 (min L (π / 3)), ENNReal.ofReal (q r) := by
    have hp : (∫⁻ r in Set.Ioc 0 L, h r * ENNReal.ofReal (L - r)) =
        ∫⁻ r in Set.Ioc 0 L, (Set.Iic (π / 3)).indicator (fun r => ENNReal.ofReal (q r)) r := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro r hr
      have hrπ : r ≤ π := le_trans hr.2 hπ
      have hs : 0 ≤ Real.sin r := Real.sin_nonneg_of_nonneg_of_le_pi hr.1.le hrπ
      have hh := hcos r hr.1.le hrπ
      by_cases ht : r ≤ π / 3
      · have hth := hh.mpr ht
        have hw : 0 ≤ wK f (Real.cos r) := by
          cases f
          · simp [wK]
          · simpa only [wK] using (show 0 ≤ Real.cos r by linarith)
        simp only [h, if_pos hth, Set.indicator, Set.mem_Iic, if_pos ht,
          abs_of_nonneg hs, q]
        rw [ENNReal.ofReal_mul (mul_nonneg (sub_nonneg.mpr hr.2) hw),
          ENNReal.ofReal_mul (sub_nonneg.mpr hr.2)]
        ac_rfl
      · have hf : ¬ (1 / 2 : ℝ) ≤ Real.cos r := fun hc => ht (hh.mp hc)
        simp only [h, if_neg hf, zero_mul, Set.indicator, Set.mem_Iic, if_neg ht]
    rw [hp, setLIntegral_indicator measurableSet_Iic]
    have hset : Set.Ioc (0 : ℝ) L ∩ Set.Iic (π / 3) = Set.Ioc 0 (min L (π / 3)) := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, le_min_iff, and_assoc]
    rw [Set.inter_comm, hset]
  have hq : Continuous q :=
    ((continuous_const.sub continuous_id).mul hc).mul Real.continuous_sin
  have hconv : ENNReal.ofReal (∫ r in Set.Ioc 0 (min L (π / 3)), q r) =
      ∫⁻ r in Set.Ioc 0 (min L (π / 3)), ENNReal.ofReal (q r) :=
    ofReal_integral_eq_lintegral_ofReal (hq.intervalIntegrable 0 (min L (π / 3))).1
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hnn))
  rw [hcut, ← hconv]
  rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
  congr 1
  dsimp [q, kK]
  rw [intervalIntegral.integral_of_le hmin]
