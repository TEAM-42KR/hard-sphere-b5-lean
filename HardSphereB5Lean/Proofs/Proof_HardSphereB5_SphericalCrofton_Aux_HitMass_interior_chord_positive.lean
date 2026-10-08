import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_unit_frame_exists
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_cap_circle_param
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt)
open scoped Classical
set_option maxHeartbeats 1500000
open Set Metric Topology

theorem proof_HardSphereB5_SphericalCrofton_Aux_HitMass_interior_chord_positive {K : Set Pt} (hK : IsRegularRegionCrofton K) (p : Pt) (hp : ‖p‖ = 1)
    (hint : (greatCircle p ∩ sInterior K).Nonempty) :
    0 < chordLen K (greatCircle p) := by
  obtain ⟨e1, e2, he3⟩ := SphereGeom.Aux.Arrangement.unit_frame_exists p hp
  have hn1 : ‖e1‖ = 1 := by simpa using he3.norm_eq_one 0
  have hn2 : ‖e2‖ = 1 := by simpa using he3.norm_eq_one 1
  have h12 : inner ℝ e1 e2 = 0 := by simpa using he3.inner_eq_zero (by decide : (0 : Fin 3) ≠ 1)
  have hp1 : inner ℝ p e1 = 0 := by simpa using he3.inner_eq_zero (by decide : (2 : Fin 3) ≠ 0)
  have hp2 : inner ℝ p e2 = 0 := by simpa using he3.inner_eq_zero (by decide : (2 : Fin 3) ≠ 1)
  have he : Orthonormal ℝ ![e1, e2] := by
    simpa [orthonormal_vecCons_iff, hn1, hn2, h12] using (show Orthonormal ℝ (![] : Fin 0 → Pt) from Orthonormal.of_isEmpty _)
  let c : ℝ → Pt := circlePt 0 e1 e2 1
  have hc : Continuous c := by
    change Continuous (fun t : ℝ => (0 : Pt) + (1 : ℝ) • (Real.cos t • e1 + Real.sin t • e2))
    fun_prop
  have hcg : ∀ t, c t ∈ greatCircle p := by
    intro t
    change ‖c t‖ = 1 ∧ inner ℝ p (c t) = 0
    constructor
    · have hsq : ‖c t‖ ^ 2 = 1 := by
        simp only [c, circlePt, one_smul, zero_add]
        rw [norm_add_sq_real]
        simp only [norm_smul, Real.norm_eq_abs, hn1, hn2, mul_one,
          real_inner_smul_left, real_inner_smul_right, h12, mul_zero, zero_mul,
          add_zero, sq_abs]
        nlinarith [Real.sin_sq_add_cos_sq t]
      nlinarith [norm_nonneg (c t)]
    · simp [c, circlePt, inner_add_right, real_inner_smul_right, hp1, hp2]
  have hparam : greatCircle p = c '' Set.Icc (0 : ℝ) (2 * π) := by
    simpa [c, greatCircle] using SphereGeom.Aux.Arrangement.cap_circle_param e1 e2 p he3 0 (by norm_num) (by norm_num)
  obtain ⟨u, huG, huI⟩ := hint
  obtain ⟨t0, ht0, hcu⟩ : u ∈ c '' Set.Icc (0 : ℝ) (2 * π) := by
    rw [← hparam]; exact huG
  let S := Metric.sphere (0 : Pt) 1
  let f : ℝ → S := fun t => ⟨c t, by simpa [S, Metric.mem_sphere] using (hcg t).1⟩
  have hf : Continuous f := hc.subtype_mk _
  let A : Set S := interior ((Subtype.val : S → Pt) ⁻¹' K)
  have hft : f t0 ∈ A := by
    obtain ⟨v, hv, hvu⟩ := huI
    have hfv : f t0 = v := Subtype.ext (hcu.trans hvu.symm)
    rw [hfv]
    exact hv
  have hopen : IsOpen (f ⁻¹' A) := isOpen_interior.preimage hf
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen t0 hft
  let d : ℝ := min (δ / 2) π
  have hd : 0 < d := lt_min (by linarith) Real.pi_pos
  have hdδ : d < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdπ : d ≤ π := min_le_right _ _
  have hsub : c '' Set.Icc t0 (t0 + d) ⊆ greatCircle p ∩ K := by
    rintro y ⟨t, ht, rfl⟩
    refine ⟨hcg t, ?_⟩
    have htd : dist t t0 < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
      linarith [ht.2]
    have htA : f t ∈ A := hball htd
    have htK : f t ∈ (Subtype.val : S → Pt) ⁻¹' K := interior_subset htA
    exact htK
  have harc : arcMeasure (c '' Set.Icc t0 (t0 + d)) = ENNReal.ofReal d := by
    simpa [c] using SphereGeom.arcMeasure_circle_arc 0 ![e1, e2] he 1 (by norm_num) t0 (t0 + d) (by linarith) (by simp; linarith [Real.pi_pos])
  have hwhole : arcMeasure (greatCircle p) = ENNReal.ofReal (2 * π) := by
    rw [hparam]
    simpa [c] using SphereGeom.arcMeasure_circle_arc 0 ![e1, e2] he 1 (by norm_num) 0 (2 * π) (by positivity) (by simp)
  have hfin : arcMeasure (greatCircle p ∩ K) ≠ ⊤ := by
    have hgfin : arcMeasure (greatCircle p) ≠ ⊤ := by
      rw [hwhole]; exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hgfin (measure_mono Set.inter_subset_left)
  have hpos : 0 < arcMeasure (greatCircle p ∩ K) := by
    have hh : 0 < arcMeasure (c '' Set.Icc t0 (t0 + d)) := by
      rw [harc]
      exact ENNReal.ofReal_pos.mpr hd
    exact lt_of_lt_of_le hh (measure_mono hsub)
  exact ENNReal.toReal_pos hpos.ne' hfin
