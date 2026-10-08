import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
set_option maxHeartbeats 1200000
private lemma g2_cdist (c : E3) (e : Fin 3 → E3) (he : Orthonormal ℝ e) (p : ℝ × ℝ) (z : ℝ) :
    dist (p.1 • e 0 + p.2 • e 1 + z • e 2) c ^ 2 =
      (p.1 - inner ℝ (e 0) c) ^ 2 + (p.2 - inner ℝ (e 1) c) ^ 2 +
      (z - inner ℝ (e 2) c) ^ 2 := by
  let b : OrthonormalBasis (Fin 3) ℝ E3 :=
    (basisOfOrthonormalOfCardEqFinrank he (by simp [E3])).toOrthonormalBasis (by simpa using he)
  have hb (i : Fin 3) : b i = e i := by simp [b]
  rw [dist_eq_norm]
  have hv := b.sum_sq_inner_right ((p.1 • e 0 + p.2 • e 1 + z • e 2) - c)
  simp only [Fin.sum_univ_three, hb, inner_sub_right, inner_add_right,
    real_inner_smul_right, orthonormal_iff_ite.mp he] at hv
  norm_num [Fin.ext_iff] at hv
  exact hv.symm

private lemma g2_circle_null (cx cy : ℝ) :
    (volume : Measure (ℝ × ℝ)) {p | (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 = 1} = 0 := by
  let A : Set (ℝ × ℝ) := {p | (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 = 1}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  rw [Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null hA
  apply Filter.Eventually.of_forall
  intro x
  have hsub : Prod.mk x ⁻¹' A ⊆ {cy - √(1 - (x - cx) ^ 2), cy + √(1 - (x - cx) ^ 2)} := by
    intro y hy
    change (x - cx) ^ 2 + (y - cy) ^ 2 = 1 at hy
    have hm : 0 ≤ 1 - (x - cx) ^ 2 := by nlinarith [sq_nonneg (y - cy)]
    have hs := sq_sqrt hm
    have heq : (y - cy) ^ 2 = √(1 - (x - cx) ^ 2) ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with hp | hm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right
      linarith
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      left
      linarith
  exact measure_mono_null hsub ((Set.finite_singleton _).insert _ |>.measure_zero (volume : Measure ℝ))

theorem proof_SolidGeom_ballInter_strict_projection_ae (n : ℕ) (hn : 0 < n)
    (c : Fin n → E3) (e : Fin 3 → E3) (he : Orthonormal ℝ e) :
    ∀ᵐ p : ℝ × ℝ ∂volume,
      (∃ z : ℝ, p.1 • e 0 + p.2 • e 1 + z • e 2 ∈
        (⋂ i, Metric.closedBall (c i) 1)) →
      ∀ i, (p.1 - inner ℝ (e 0) (c i)) ^ 2 +
        (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1 := by   classical
  have hpair (i : Fin n) : ∀ᵐ p : ℝ × ℝ ∂volume,
      (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 ≠ 1 := by
    exact measure_eq_zero_iff_ae_notMem.mp (g2_circle_null _ _)
  have ha : ∀ᵐ p : ℝ × ℝ ∂volume, ∀ i,
      (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 ≠ 1 :=
    ae_all_iff.mpr hpair
  filter_upwards [ha] with p hp
  rintro ⟨z, hz⟩ i
  have hmem := Set.mem_iInter.mp hz i
  rw [Metric.mem_closedBall] at hmem
  have hsq := (sq_le_sq₀ dist_nonneg zero_le_one).mpr hmem
  rw [g2_cdist (c i) e he p z] at hsq
  have hle : (p.1 - inner ℝ (e 0) (c i)) ^ 2 +
      (p.2 - inner ℝ (e 1) (c i)) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (z-inner ℝ (e 2) (c i))]
  exact lt_of_le_of_ne hle (hp i)

