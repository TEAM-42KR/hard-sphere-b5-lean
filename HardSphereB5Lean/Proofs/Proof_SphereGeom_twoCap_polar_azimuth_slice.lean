import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real

set_option maxHeartbeats 800000

private theorem azimuthOverlap_length_aux (f g alpha : ℝ) (hf : 0 ≤ f) (hfp : f ≤ π / 2)
    (hg : 0 ≤ g) (hgp : g ≤ π / 2) (ha : 0 ≤ alpha) (hap : alpha ≤ π) :
    (volume {phi : ℝ | phi ∈ Set.Ioc (-π) π ∧ cos phi ≥ cos f ∧ cos (phi - alpha) ≥ cos g}).toReal =
      max 0 (min (2 * f) (min (2 * g) (f + g - alpha))) := by
  have hcos (x r : ℝ) (hr0 : 0 ≤ r) (hrp : r ≤ π) (hxp : |x| ≤ π) :
      cos r ≤ cos x ↔ |x| ≤ r := by
    rw [← cos_abs x]
    constructor
    · intro h
      by_contra hn
      have hc := cos_lt_cos_of_nonneg_of_le_pi hr0 hxp (lt_of_not_ge hn)
      exact (not_lt_of_ge h) hc
    · intro h
      exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) hrp h
  have hnull : ∀ᵐ x : ℝ ∂volume, x ≠ -(π / 2) := by
    rw [ae_iff]
    simp
  have hset :
      {phi : ℝ | phi ∈ Set.Ioc (-π) π ∧ cos phi ≥ cos f ∧ cos (phi - alpha) ≥ cos g}
        =ᵐ[volume] Set.Icc (max (-f) (alpha - g)) (min f (alpha + g)) := by
    filter_upwards [hnull] with phi hne
    apply propext
    change (phi ∈ Set.Ioc (-π) π ∧ cos phi ≥ cos f ∧ cos (phi - alpha) ≥ cos g) ↔
      phi ∈ Set.Icc (max (-f) (alpha - g)) (min f (alpha + g))
    constructor
    · rintro ⟨hp, hcf, hcg⟩
      have habsf := (hcos phi f hf (by linarith [pi_pos])
        (abs_le.mpr ⟨le_of_lt hp.1, hp.2⟩)).mp hcf
      have hpf := abs_le.mp habsf
      have hlow : -π ≤ phi - alpha := by
        by_contra hn
        have ht : phi - alpha < -π := lt_of_not_ge hn
        have h0 : 0 ≤ phi - alpha + 2 * π := by linarith [pi_pos]
        have hpi : phi - alpha + 2 * π ≤ π := by linarith
        have hc : cos g ≤ cos (phi - alpha + 2 * π) := by
          simpa only [cos_add_two_pi] using hcg
        have hb := (hcos (phi - alpha + 2 * π) g hg (by linarith [pi_pos])
          (abs_le.mpr ⟨by linarith, hpi⟩)).mp hc
        rw [abs_of_nonneg h0] at hb
        have heq : phi = -(π / 2) := by linarith
        exact hne heq
      have habsg := (hcos (phi - alpha) g hg (by linarith [pi_pos])
        (abs_le.mpr ⟨hlow, by linarith [pi_pos]⟩)).mp hcg
      have hpg := abs_le.mp habsg
      exact ⟨max_le hpf.1 (by linarith), le_min hpf.2 (by linarith)⟩
    · intro hp
      have hpf : -f ≤ phi ∧ phi ≤ f := ⟨(max_le_iff.mp hp.1).1, (le_min_iff.mp hp.2).1⟩
      have hpg : -g ≤ phi - alpha ∧ phi - alpha ≤ g := by
        constructor
        · have := (max_le_iff.mp hp.1).2; linarith
        · have := (le_min_iff.mp hp.2).2; linarith
      refine ⟨⟨by linarith [pi_pos], by linarith [pi_pos]⟩, ?_, ?_⟩
      · apply (hcos phi f hf (by linarith [pi_pos])
          (abs_le.mpr ⟨by linarith [pi_pos], by linarith [pi_pos]⟩)).mpr
        exact abs_le.mpr hpf
      · apply (hcos (phi - alpha) g hg (by linarith [pi_pos])
          (abs_le.mpr ⟨by linarith [pi_pos], by linarith [pi_pos]⟩)).mpr
        exact abs_le.mpr hpg
  rw [measure_congr hset, Real.volume_Icc, ENNReal.toReal_ofReal']
  rw [max_comm _ (0 : ℝ)]
  by_cases hfg : f ≤ alpha + g
  · rw [min_eq_left hfg]
    by_cases hleft : -f ≤ alpha - g
    · rw [max_eq_right hleft]
      have h1 : f + g - alpha ≤ 2 * f := by linarith
      have h2 : f + g - alpha ≤ 2 * g := by linarith
      rw [min_eq_right h2, min_eq_right h1]
      congr 1
      ring
    · rw [max_eq_left (le_of_not_ge hleft)]
      have h1 : 2 * f ≤ f + g - alpha := by linarith
      have h2 : 2 * f ≤ 2 * g := by linarith
      rw [← min_assoc, min_eq_left h2, min_eq_left h1]
      congr 1
      ring
  · rw [min_eq_right (le_of_not_ge hfg)]
    have hleft : -f ≤ alpha - g := by linarith
    rw [max_eq_right hleft]
    have h1 : 2 * g ≤ 2 * f := by linarith
    have h2 : 2 * g ≤ f + g - alpha := by linarith
    rw [min_eq_left h2, min_eq_right h1]
    congr 1
    ring

open SphereGeom

private theorem polarFrame_twoCap_iff_aux (e : Fin 3 → E3) (he : Orthonormal ℝ e)
 (d s h k θ φ α : ℝ) :
 let u := (Real.sin θ * Real.cos φ) • e 0 + (Real.sin θ * Real.sin φ) • e 1 + Real.cos θ • e 2
 u ∈ cap (d • e 0) h ∩ cap (s • (Real.cos α • e 0 + Real.sin α • e 1)) k ↔
 h ≤ d * Real.sin θ * Real.cos φ ∧ k ≤ s * Real.sin θ * Real.cos (φ - α) := by
  dsimp only
  let u := (Real.sin θ * Real.cos φ) • e 0 + (Real.sin θ * Real.sin φ) • e 1 + Real.cos θ • e 2
  have hi := orthonormal_iff_ite.mp he
  have hu2 : ‖u‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [u]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hi, he.norm_eq_one]
    norm_num [Fin.ext_iff]
    have hp : Real.sin θ ^ 2 * (Real.sin φ ^ 2 + Real.cos φ ^ 2) = Real.sin θ ^ 2 := by
      rw [Real.sin_sq_add_cos_sq, mul_one]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hu : ‖u‖ = 1 := by nlinarith [norm_nonneg u]
  have hd : inner ℝ (d • e 0) u = d * Real.sin θ * Real.cos φ := by
    dsimp [u]
    simp [inner_add_right, real_inner_smul_left, real_inner_smul_right, hi, he.norm_eq_one]
    ring
  have hs : inner ℝ (s • (Real.cos α • e 0 + Real.sin α • e 1)) u =
      s * Real.sin θ * Real.cos (φ - α) := by
    dsimp [u]
    simp [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hi, he.norm_eq_one, Real.cos_sub]
    ring
  change (‖u‖ = 1 ∧ h ≤ inner ℝ (d • e 0) u) ∧
      (‖u‖ = 1 ∧ k ≤ inner ℝ (s • (Real.cos α • e 0 + Real.sin α • e 1)) u) ↔ _
  simp only [hu, hd, hs, true_and]

private theorem cosine_overlap_integral_aux (r k l alpha : ℝ)
    (hr : 0 < r) (hk : 0 < k) (hl : 0 < l) (ha : 0 ≤ alpha) (hap : alpha ≤ π) :
    (∫ phi in (0 : ℝ)..(2 * π),
      {phi : ℝ | k ≤ r * cos phi ∧ l ≤ r * cos (phi - alpha)}.indicator
        (fun _ : ℝ => (1 : ℝ)) phi) =
      max 0 (min (2 * arccos (k / r))
        (min (2 * arccos (l / r)) (arccos (k / r) + arccos (l / r) - alpha))) := by
  classical
  let S : Set ℝ := {phi : ℝ | k ≤ r * cos phi ∧ l ≤ r * cos (phi - alpha)}
  change (∫ phi in (0 : ℝ)..(2 * π), S.indicator (fun _ => (1 : ℝ)) phi) = _
  have hmS : MeasurableSet S :=
    (isClosed_le continuous_const (by fun_prop : Continuous (fun phi : ℝ => r * cos phi))).measurableSet.inter
      (isClosed_le continuous_const (by fun_prop : Continuous (fun phi : ℝ => r * cos (phi - alpha)))).measurableSet
  have hzero (q : ℝ) (hq : ¬ q / r ≤ 1) : arccos (q / r) = 0 :=
    arccos_eq_zero.mpr (le_of_lt (lt_of_not_ge hq))
  have hempty (q : ℝ) (hq : ¬ q / r ≤ 1) (t : ℝ) : ¬ q ≤ r * cos t := by
    have hqr : r < q := (one_lt_div hr).mp (lt_of_not_ge hq)
    have hrc := mul_le_mul_of_nonneg_left (cos_le_one t) hr.le
    intro ht
    linarith
  by_cases hk1 : k / r ≤ 1
  · by_cases hl1 : l / r ≤ 1
    · let f := arccos (k / r)
      let g := arccos (l / r)
      have hf : 0 ≤ f := arccos_nonneg _
      have hg : 0 ≤ g := arccos_nonneg _
      have hfp : f ≤ π / 2 := arccos_le_pi_div_two.mpr (div_nonneg hk.le hr.le)
      have hgp : g ≤ π / 2 := arccos_le_pi_div_two.mpr (div_nonneg hl.le hr.le)
      have hcf : cos f = k / r := cos_arccos (by linarith [div_nonneg hk.le hr.le]) hk1
      have hcg : cos g = l / r := cos_arccos (by linarith [div_nonneg hl.le hr.le]) hl1
      have hper : Function.Periodic (S.indicator (fun _ => (1 : ℝ))) (2 * π) := by
        intro phi
        have hmem : phi + 2 * π ∈ S ↔ phi ∈ S := by
          dsimp [S]
          rw [cos_add_two_pi, show phi + 2 * π - alpha = (phi - alpha) + 2 * π by ring,
            cos_add_two_pi]
        by_cases hx : phi ∈ S
        · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem (fun h => hx (hmem.mp h)), Set.indicator_of_notMem hx]
      have hset : S ∩ Set.Ioc (-π) π =
          {phi : ℝ | phi ∈ Set.Ioc (-π) π ∧ cos phi ≥ cos f ∧ cos (phi - alpha) ≥ cos g} := by
        ext phi
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, S, hcf, hcg]
        change (k ≤ r * cos phi ∧ l ≤ r * cos (phi - alpha)) ∧ phi ∈ Set.Ioc (-π) π ↔
          phi ∈ Set.Ioc (-π) π ∧ k / r ≤ cos phi ∧ l / r ≤ cos (phi - alpha)
        rw [div_le_iff₀ hr, div_le_iff₀ hr]
        simp only [mul_comm r]
        tauto
      calc
        (∫ phi in (0 : ℝ)..(2 * π), S.indicator (fun _ => (1 : ℝ)) phi) =
            ∫ phi in (-π)..π, S.indicator (fun _ => (1 : ℝ)) phi := by
          simpa only [zero_add, show -π + 2 * π = π by ring] using hper.intervalIntegral_add_eq 0 (-π)
        _ = (volume (S ∩ Set.Ioc (-π) π)).toReal := by
          rw [intervalIntegral.integral_of_le (by linarith [pi_pos])]
          rw [integral_indicator_const (1 : ℝ) hmS, measureReal_def, Measure.restrict_apply hmS]
          simp [smul_eq_mul]
        _ = max 0 (min (2 * f) (min (2 * g) (f + g - alpha))) := by
          rw [hset]
          exact azimuthOverlap_length_aux f g alpha hf hfp hg hgp ha hap
    · have hS : S = ∅ := by
        ext phi
        simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hx => hempty l hl1 (phi - alpha) hx.2
      rw [hS, hzero l hl1]
      simp only [Set.indicator_empty, intervalIntegral.integral_zero, mul_zero]
      symm
      exact max_eq_left ((min_le_right _ _).trans (min_le_left _ _))
  · have hS : S = ∅ := by
      ext phi
      simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hempty k hk1 phi hx.1
    rw [hS, hzero k hk1]
    simp only [Set.indicator_empty, intervalIntegral.integral_zero, mul_zero]
    symm
    exact max_eq_left (min_le_left _ _)

theorem proof_SphereGeom_twoCap_polar_azimuth_slice (e : Fin 3 → E3) (he : Orthonormal ℝ e)
    (k l alpha theta : ℝ) (hk : 0 < k) (hl : 0 < l)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ π) (ht0 : 0 < theta) (ht1 : theta < π) :
    let f := arccos (k / sqrt (1 - cos theta ^ 2))
    let g := arccos (l / sqrt (1 - cos theta ^ 2))
    (∫ phi in (0 : ℝ)..(2 * π),
      (cap (e 0) k ∩ cap (cos alpha • e 0 + sin alpha • e 1) l).indicator
      (fun _ : E3 => (1 : ℝ))
      ((sin theta * cos phi) • e 0 + (sin theta * sin phi) • e 1 + cos theta • e 2)) =
      max 0 (min (2 * f) (min (2 * g) (f + g - alpha))) := by
  classical
  dsimp only
  have hsin : 0 < sin theta := sin_pos_of_pos_of_lt_pi ht0 ht1
  have hsqrt : sqrt (1 - cos theta ^ 2) = sin theta := by
    rw [show 1 - cos theta ^ 2 = sin theta ^ 2 by nlinarith [sin_sq_add_cos_sq theta], sqrt_sq hsin.le]
  rw [hsqrt]
  have H := cosine_overlap_integral_aux (sin theta) k l alpha hsin hk hl ha0 ha1
  rw [← H]
  apply intervalIntegral.integral_congr
  intro phi hphi
  dsimp only
  have hiff := polarFrame_twoCap_iff_aux e he 1 1 k l theta phi alpha
  simp only [one_smul, one_mul] at hiff
  by_cases hp : k ≤ sin theta * cos phi ∧ l ≤ sin theta * cos (phi - alpha)
  · have hp' : phi ∈ {phi : ℝ | k ≤ sin theta * cos phi ∧ l ≤ sin theta * cos (phi - alpha)} := hp
    rw [Set.indicator_of_mem (hiff.mpr hp), Set.indicator_of_mem hp']
  · have hp' : phi ∉ {phi : ℝ | k ≤ sin theta * cos phi ∧ l ≤ sin theta * cos (phi - alpha)} := hp
    rw [Set.indicator_of_notMem (fun h => hp (hiff.mp h)), Set.indicator_of_notMem hp']
