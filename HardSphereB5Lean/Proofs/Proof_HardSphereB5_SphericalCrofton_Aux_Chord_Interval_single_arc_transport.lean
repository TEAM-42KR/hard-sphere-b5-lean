import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_double_interval
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_ArcLength_restrict_circle_arc_eq_map
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_single_arc_transport {K : Set Pt} (f : Kern) (E1 E2 p : Pt)
    (hE : Orthonormal ℝ ![E1, E2, p]) (a b : ℝ) (hab : a ≤ b) (hπ : b - a ≤ π)
    (hgeom : greatCircle p ∩ K = circlePt 0 E1 E2 1 '' Set.Icc a b) :
    (∫⁻ u in greatCircle p ∩ K, ∫⁻ v in greatCircle p ∩ K,
      (if (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0) *
        ENNReal.ofReal (Real.sqrt (1 - (inner ℝ u v) ^ 2)) ∂arcMeasure ∂arcMeasure) =
      ENNReal.ofReal (kK f (b - a)) ∧ chordLen K (greatCircle p) = b - a := by
  have h0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hb : b - a ≤ 2 * π := by linarith [Real.pi_pos]
  have h00 : inner ℝ E1 E1 = 1 := by
    simpa using (orthonormal_iff_ite.mp hE (0 : Fin 3) 0)
  have h01 : inner ℝ E1 E2 = 0 := by
    simpa using (orthonormal_iff_ite.mp hE (0 : Fin 3) 1)
  have h10 : inner ℝ E2 E1 = 0 := by
    simpa using (orthonormal_iff_ite.mp hE (1 : Fin 3) 0)
  have h11 : inner ℝ E2 E2 = 1 := by
    simpa using (orthonormal_iff_ite.mp hE (1 : Fin 3) 1)
  have he2 : Orthonormal ℝ ![E1, E2] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  let φ : ℝ → Pt := circlePt 0 E1 E2 1
  have hφ : Measurable φ := by
    have hc : Continuous (fun t : ℝ => circlePt 0 E1 E2 1 t) := by
      unfold circlePt
      fun_prop
    exact hc.measurable
  have hinner (s t : ℝ) : inner ℝ (φ s) (φ t) = Real.cos (s - t) := by
    simp only [φ, circlePt, zero_add, one_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, h00, h01, h10, h11,
      mul_one, mul_zero, zero_mul, add_zero, zero_add]
    rw [Real.cos_sub]
    ring
  have hsqrt (s t : ℝ) : Real.sqrt (1 - Real.cos (s - t) ^ 2) = |Real.sin (s - t)| := by
    rw [show 1 - Real.cos (s - t) ^ 2 = Real.sin (s - t) ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq (s - t)]]
    exact Real.sqrt_sq_eq_abs _
  let ν : Measure ℝ := volume.restrict (Set.Icc a b)
  have hmap : arcMeasure.restrict (greatCircle p ∩ K) = ν.map φ := by
    rw [hgeom]
    simpa [ν, φ] using
      (SphereGeom.Aux.ArcLength.restrict_circle_arc_eq_map 0 ![E1, E2] he2 1
        (by norm_num) a b hab hb)
  have hmass : arcMeasure (φ '' Set.Icc a b) = ENNReal.ofReal (b - a) := by
    simpa [φ] using (SphereGeom.arcMeasure_circle_arc 0 ![E1, E2] he2 1
      (by norm_num) a b hab hb)
  constructor
  · let H : Pt → Pt → ENNReal := fun u v =>
      (if (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0) *
        ENNReal.ofReal (Real.sqrt (1 - (inner ℝ u v) ^ 2))
    have hw : Measurable (fun z : Pt × Pt => wK f (inner ℝ z.1 z.2)) := by
      cases f
      · exact measurable_const
      · exact measurable_fst.inner measurable_snd
    have hH : Measurable (fun z : Pt × Pt => H z.1 z.2) := by
      apply Measurable.mul
      · exact Measurable.ite (measurableSet_le measurable_const
          (measurable_fst.inner measurable_snd))
          (ENNReal.measurable_ofReal.comp hw) measurable_const
      · exact ENNReal.measurable_ofReal.comp
          (Real.continuous_sqrt.measurable.comp
            (measurable_const.sub ((measurable_fst.inner measurable_snd).pow_const 2)))
    let h : ℝ → ENNReal := fun r =>
      (if (1 / 2 : ℝ) ≤ Real.cos r then ENNReal.ofReal (wK f (Real.cos r)) else 0) *
        ENNReal.ofReal |Real.sin r|
    have hshift (g : ℝ → ENNReal) : (∫⁻ x in Set.Icc a b, g x) =
        ∫⁻ x in Set.Icc 0 (b - a), g (a + x) := by
      symm
      have hp := (measurePreserving_add_left (volume : Measure ℝ) a).setLIntegral_comp_emb
        (Homeomorph.addLeft a).measurableEmbedding g (Set.Icc 0 (b - a))
      simpa only [Set.image_const_add_Icc, add_zero,
        show a + (b - a) = b by ring] using hp
    rw [hmap]
    change (∫⁻ u, ∫⁻ v, H u v ∂ν.map φ ∂ν.map φ) = _
    calc
      (∫⁻ u, ∫⁻ v, H u v ∂ν.map φ ∂ν.map φ) =
          ∫⁻ u, ∫⁻ t, H u (φ t) ∂ν ∂ν.map φ := by
        apply lintegral_congr
        intro u
        exact lintegral_map (hH.comp (measurable_const.prodMk measurable_id)) hφ
      _ = ∫⁻ s, ∫⁻ t, H (φ s) (φ t) ∂ν ∂ν := by
        exact lintegral_map
          ((hH.comp (measurable_fst.prodMk (hφ.comp measurable_snd))).lintegral_prod_right') hφ
      _ = ∫⁻ s in Set.Icc a b, ∫⁻ t in Set.Icc a b, h (s - t) := by
        apply lintegral_congr
        intro s
        apply lintegral_congr
        intro t
        dsimp [H, h]
        rw [hinner, hsqrt]
      _ = ∫⁻ s in Set.Icc 0 (b - a), ∫⁻ t in Set.Icc 0 (b - a), h (s - t) := by
        rw [hshift]
        apply lintegral_congr
        intro s
        rw [hshift]
        apply lintegral_congr
        intro t
        congr 1
        ring
      _ = ENNReal.ofReal (kK f (b - a)) := by
        simpa only [restrict_Ioc_eq_restrict_Icc, h] using
          (HardSphereB5.SphericalCrofton.Aux.Chord.Interval.double_interval f (b - a) h0 hπ)
  · change (arcMeasure (greatCircle p ∩ K)).toReal = b - a
    rw [hgeom]
    change (arcMeasure (φ '' Set.Icc a b)).toReal = b - a
    rw [hmass, ENNReal.toReal_ofReal h0]
