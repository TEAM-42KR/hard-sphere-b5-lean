import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
open Filter Topology

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_positive_caps_pair_straddles (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hpos : ∀ i, 0 < h i) (u v p : Pt)
    (hus : ‖u‖ = 1) (hvs : ‖v‖ = 1) (hpn : ‖p‖ = 1)
    (hu : ∀ i, h i ≤ inner ℝ (n i) u)
    (hv : ∀ i, h i ≤ inner ℝ (n i) v)
    (huv : u ≠ v) (hnon : u ≠ -v)
    (hpu : inner ℝ p u = 0) (hpv : inner ℝ p v = 0) :
    (∃ a ∈ ⋂ i, cap (n i) (h i), inner ℝ p a < 0) ∧
      (∃ b ∈ ⋂ i, cap (n i) (h i), 0 < inner ℝ p b) := by
  classical
  have hsum0 : u + v ≠ 0 := fun hh => hnon (eq_neg_of_add_eq_zero_left hh)
  have hs0 : 0 < ‖u + v‖ := norm_pos_iff.mpr hsum0
  have hdist : 0 < ‖u - v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr huv))
  have hs2 : ‖u + v‖ ^ 2 < 4 := by
    have hh := parallelogram_law_with_norm ℝ u v
    rw [hus, hvs] at hh
    nlinarith
  have hs : ‖u + v‖ < 2 := by nlinarith [norm_nonneg (u + v)]
  let w : Pt := ‖u + v‖⁻¹ • (u + v)
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0), inv_mul_cancel₀ hs0.ne']
  have hpw : inner ℝ p w = 0 := by simp [w, inner_smul_right, inner_add_right, hpu, hpv]
  have hstrict : ∀ i, h i < inner ℝ (n i) w := by
    intro i
    dsimp [w]
    rw [inner_smul_right, inner_add_right, inv_mul_eq_div]
    apply (lt_div_iff₀ hs0).mpr
    have hi : 2 * h i ≤ inner ℝ (n i) u + inner ℝ (n i) v := by linarith [hu i, hv i]
    nlinarith [hpos i]
  let raw : ℝ → Pt := fun t => w + t • p
  let F : ℝ → Pt := fun t => unitDir (raw t)
  have hraw0 : ∀ t, raw t ≠ 0 := by
    intro t ht
    have hwself : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
    have hwp : inner ℝ w p = 0 := by rw [real_inner_comm, hpw]
    have hh : inner ℝ w (raw t) = 1 := by simp only [raw, inner_add_right, inner_smul_right, hwself, hwp, mul_zero, add_zero]
    rw [ht, inner_zero_right] at hh
    norm_num at hh
  have hF0 : F 0 = w := by simp [F, raw, unitDir, hw]
  have hrawc : Continuous raw := by dsimp [raw]; fun_prop
  have hFc : ContinuousAt F 0 := by
    exact (hrawc.norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr (hraw0 0))).smul hrawc.continuousAt
  have hgood : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, h i < inner ℝ (n i) (F t) := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t => inner ℝ (n i) (F t)) 0 :=
      continuousAt_const.inner hFc
    apply hc.eventually (isOpen_Ioi.mem_nhds ?_)
    simpa only [hF0, Set.mem_Ioi] using hstrict i
  obtain ⟨ε, hε, heps⟩ := Metric.eventually_nhds_iff.mp hgood
  have hFnorm : ∀ t, ‖F t‖ = 1 := by
    intro t
    change ‖‖raw t‖⁻¹ • raw t‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr (hraw0 t))),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hraw0 t))]
  have hinner : ∀ t, inner ℝ p (F t) = ‖raw t‖⁻¹ * t := by
    intro t
    have hpp : inner ℝ p p = 1 := by rw [real_inner_self_eq_norm_sq, hpn]; norm_num
    simp only [F, unitDir, raw, inner_smul_right, inner_add_right, hpw, hpp, mul_one, zero_add]
  have hmem (t : ℝ) (ht : |t| < ε) : F t ∈ ⋂ i, cap (n i) (h i) := by
    apply Set.mem_iInter.mpr
    intro i
    refine ⟨hFnorm t, (heps (by simpa [Real.dist_eq] using ht) i).le⟩
  refine ⟨⟨F (-ε / 2), hmem _ (by rw [abs_of_neg (by linarith)]; linarith), ?_⟩,
    ⟨F (ε / 2), hmem _ (by rw [abs_of_pos (by linarith)]; linarith), ?_⟩⟩
  · rw [hinner]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr (hraw0 _))) (by linarith)
  · rw [hinner]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (hraw0 _))) (by linarith)
