import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_measurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_label_geometry
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_restrict_union_null
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pole_orientation
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_positive_caps_pair_straddles
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_sigma_caps_data
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_frontier_slice
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_sigma_axis_cases
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_pair_transverse_ae (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)) :
    ∀ᵐ q ∂weightedPairMu D, ‖pairPole q‖ = 1 ∧ q.1 ≠ q.2 ∧
      q.1 ∈ greatCircle (pairPole q) ∩ sFrontier (SigmaD D) ∧
      q.2 ∈ greatCircle (pairPole q) ∩ sFrontier (SigmaD D) ∧
      (∃ u ∈ SigmaD D, inner ℝ (pairPole q) u < 0) ∧
      (∃ v ∈ SigmaD D, 0 < inner ℝ (pairPole q) v) := by
  classical
  have heN : ‖e‖ = 1 := by simp [HardSphereB5.Lean.e]
  have hsupport (u : Pt) (hu : u ∈ arcA D ∪ arcB D) : u ∈ SigmaD D := by
    rcases hu with hu | hu
    · by_cases h0 : D = 0
      · simp [arcA, h0] at hu
      · simp only [arcA, if_neg h0, Set.mem_setOf_eq] at hu
        exact hu.1
    · by_cases he : D = e
      · simp [arcB, he] at hu
      · simp only [arcB, if_neg he, Set.mem_setOf_eq] at hu
        exact hu.1
  have hboundary (u : Pt) (hu : u ∈ arcA D ∪ arcB D) : u ∈ sFrontier (SigmaD D) := by
    by_cases h0 : D = 0
    · subst D
      rw [sigma_axis_cases.2.1.1, Aux.Cap.frontier_slice e heN (1 / 2)
        (by norm_num) (by norm_num)]
      simpa only [sigma_axis_cases.2.1.2.1, sigma_axis_cases.2.1.2.2, Set.empty_union] using hu
    by_cases he : D = e
    · subst D
      rw [sigma_axis_cases.2.2.1, Aux.Cap.frontier_slice (-e) (by simpa using heN) (1 / 2)
        (by norm_num) (by norm_num)]
      simpa only [sigma_axis_cases.2.2.2.1, sigma_axis_cases.2.2.2.2, Set.union_empty] using hu
    have hna : ‖D‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hD.1
    have hnb : ‖D - e‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hD.2
    have ha : 0 < ‖D‖ := norm_pos_iff.mpr h0
    have hb : 0 < ‖D - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
    obtain ⟨hnA, hnB, hcaps⟩ := Aux.Cap.sigma_caps_data D h0 he
    have hbnd (K : Set Pt) (hsub : SigmaD D ⊆ K) (hus : u ∈ SigmaD D)
        (hf : u ∈ sFrontier K) : u ∈ sFrontier (SigmaD D) := by
      rcases hf with ⟨y, hy, rfl⟩
      have hys : y ∈ (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' SigmaD D := hus
      refine ⟨y, (mem_frontier_iff_notMem_interior hys).2 ?_, rfl⟩
      intro hi
      exact hy.2 (interior_mono (Set.preimage_mono hsub) hi)
    have hface (d : Pt) (hd : d ≠ 0) (hus : ‖u‖ = 1) (hdu : ‖d + u‖ = 1) :
        inner ℝ (‖d‖⁻¹ • (-d)) u = ‖d‖ / 2 := by
      have hs := norm_add_sq_real d u
      rw [hus, hdu] at hs
      have hi : inner ℝ d u = -‖d‖^2 / 2 := by nlinarith
      rw [real_inner_smul_left, inner_neg_left, hi]
      field_simp [norm_ne_zero_iff.mpr hd]
    rcases hu with hu | hu
    · simp only [arcA, if_neg h0, Set.mem_setOf_eq] at hu
      apply hbnd (cap (nAv D) (‖D‖ / 2)) (by rw [hcaps]; exact Set.inter_subset_left) hu.1
      rw [Aux.Cap.frontier_slice (nAv D) hnA (‖D‖ / 2) (by linarith) (by linarith)]
      exact ⟨hu.1.1, hface D h0 hu.1.1 hu.2⟩
    · simp only [arcB, if_neg he, Set.mem_setOf_eq] at hu
      apply hbnd (cap (nBv D) (‖D - e‖ / 2)) (by rw [hcaps]; exact Set.inter_subset_right) hu.1
      rw [Aux.Cap.frontier_slice (nBv D) hnB (‖D - e‖ / 2) (by linarith) (by linarith)]
      refine ⟨hu.1.1, ?_⟩
      have hdu : ‖(D - e) + u‖ = 1 := by
        simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hu.2
      simpa only [nBv, show e - D = -(D - e) by abel] using
        hface (D - e) (sub_ne_zero.mpr he) hu.1.1 hdu
  have hg := boundary_label_geometry D hD hK
  letI : IsFiniteMeasure (arcMeasure.restrict (arcA D)) := ⟨by simpa using hg.2.2.2.1⟩
  letI : IsFiniteMeasure (arcMeasure.restrict (arcB D)) := ⟨by simpa using hg.2.2.2.2⟩
  letI : IsFiniteMeasure (boundaryMu D) := by
    unfold boundaryMu
    rw [restrict_union_null arcMeasure (arcA D) (arcB D) hg.2.1 hg.2.2.1]
    infer_instance
  have hbase : ∀ᵐ u ∂boundaryMu D, u ∈ arcA D ∪ arcB D :=
    ae_restrict_mem (hg.1.union hg.2.1)
  have hfirst : ∀ᵐ q ∂pairMu D, q.1 ∈ arcA D ∪ arcB D :=
    Measure.quasiMeasurePreserving_fst.ae hbase
  have hsecond : ∀ᵐ q ∂pairMu D, q.2 ∈ arcA D ∪ arcB D :=
    Measure.quasiMeasurePreserving_snd.ae hbase
  rcases pair_measurable D with ⟨_, _, _, _, hmeas, _⟩
  unfold weightedPairMu
  apply (ae_withDensity_iff hmeas.ennreal_ofReal).mpr
  filter_upwards [hfirst, hsecond] with q hq1 hq2
  intro hweight
  have hcross : cross q.1 q.2 ≠ 0 := by
    intro hz
    apply hweight
    simp [pairDens, santaloDens, hz]
  have huv : q.1 ≠ q.2 := by
    intro hh
    apply hcross
    rw [hh]
    ext i
    fin_cases i <;> simp [cross, cross_apply] <;> ring
  have hnon : q.1 ≠ -q.2 := by
    intro hh
    apply hcross
    rw [hh]
    ext i
    fin_cases i <;> simp [cross, cross_apply] <;> ring
  have hs1 := hsupport q.1 hq1
  have hs2 := hsupport q.2 hq2
  have hn1 : ‖q.1‖ = 1 := hs1.1
  have hn2 : ‖q.2‖ = 1 := hs2.1
  have hp := pole_orientation q.1 q.2
  have hpn : ‖pairPole q‖ = 1 := hp.2.2.2 hcross
  have hpu : inner ℝ (pairPole q) q.1 = 0 := hp.2.1
  have hpv : inner ℝ (pairPole q) q.2 = 0 := hp.2.2.1
  have hstraddle : (∃ a ∈ SigmaD D, inner ℝ (pairPole q) a < 0) ∧
      (∃ b ∈ SigmaD D, 0 < inner ℝ (pairPole q) b) := by
    by_cases h0 : D = 0
    · rw [h0, sigma_axis_cases.2.1.1] at hs1 hs2 ⊢
      simpa only [Set.iInter_const] using
        positive_caps_pair_straddles 1 (fun _ => e) (fun _ => (1 / 2 : ℝ))
          (fun _ => by norm_num) q.1 q.2 (pairPole q) hn1 hn2 hpn
          (fun _ => hs1.2) (fun _ => hs2.2) huv hnon hpu hpv
    by_cases he : D = e
    · rw [he, sigma_axis_cases.2.2.1] at hs1 hs2 ⊢
      simpa only [Set.iInter_const] using
        positive_caps_pair_straddles 1 (fun _ => -e) (fun _ => (1 / 2 : ℝ))
          (fun _ => by norm_num) q.1 q.2 (pairPole q) hn1 hn2 hpn
          (fun _ => hs1.2) (fun _ => hs2.2) huv hnon hpu hpv
    obtain ⟨_, _, hrep⟩ := Aux.Cap.sigma_caps_data D h0 he
    let n : Fin 2 → Pt := ![nAv D, nBv D]
    let h : Fin 2 → ℝ := ![‖D‖ / 2, ‖D - e‖ / 2]
    have hpos : ∀ i, 0 < h i := by
      intro i
      have ha : 0 < ‖D‖ := norm_pos_iff.mpr h0
      have hb : 0 < ‖D - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
      fin_cases i <;> simp only [h, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · exact div_pos ha (by norm_num)
      · exact div_pos hb (by norm_num)
    have hset : (⋂ i, cap (n i) (h i)) = SigmaD D := by
      rw [hrep]
      ext u
      simp [n, h, Set.mem_iInter, Fin.forall_fin_two]
    have hcu : ∀ i, h i ≤ inner ℝ (n i) q.1 :=
      fun i => (Set.mem_iInter.mp (hset.symm ▸ hs1) i).2
    have hcv : ∀ i, h i ≤ inner ℝ (n i) q.2 :=
      fun i => (Set.mem_iInter.mp (hset.symm ▸ hs2) i).2
    simpa only [hset] using positive_caps_pair_straddles 2 n h hpos q.1 q.2
      (pairPole q) hn1 hn2 hpn hcu hcv huv hnon hpu hpv
  exact ⟨hpn, huv, ⟨⟨hn1, hpu⟩, hboundary q.1 hq1⟩,
    ⟨⟨hn2, hpv⟩, hboundary q.2 hq2⟩, hstraddle.1, hstraddle.2⟩
