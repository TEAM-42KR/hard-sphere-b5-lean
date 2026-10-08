import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SolidGeom_projected_sphere_tie_null
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
private lemma g2_graph_mem (c : E3) (e : Fin 3 → E3) (he : Orthonormal ℝ e) (p : ℝ × ℝ)
    (hp : (p.1 - inner ℝ (e 0) c) ^ 2 + (p.2 - inner ℝ (e 1) c) ^ 2 < 1) :
    p.1 • e 0 + p.2 • e 1 +
      (inner ℝ (e 2) c + √(1 - (p.1 - inner ℝ (e 0) c) ^ 2 -
        (p.2 - inner ℝ (e 1) c) ^ 2)) • e 2 ∈ Metric.sphere c 1 := by
  rw [Metric.mem_sphere]
  have hn := g2_cdist c e he p (inner ℝ (e 2) c + √(1 -
    (p.1 - inner ℝ (e 0) c) ^ 2 - (p.2 - inner ℝ (e 1) c) ^ 2))
  have hm : 0 ≤ 1 - (p.1 - inner ℝ (e 0) c) ^ 2 -
    (p.2 - inner ℝ (e 1) c) ^ 2 := by linarith
  have hs := sq_sqrt hm
  have heq : dist (p.1 • e 0 + p.2 • e 1 + (inner ℝ (e 2) c +
    √(1 - (p.1 - inner ℝ (e 0) c) ^ 2 - (p.2 - inner ℝ (e 1) c) ^ 2)) • e 2) c ^ 2 = 1 := by
    nlinarith [hn]
  have hd : 0 ≤ dist (p.1 • e 0 + p.2 • e 1 + (inner ℝ (e 2) c +
    √(1 - (p.1 - inner ℝ (e 0) c) ^ 2 - (p.2 - inner ℝ (e 1) c) ^ 2)) • e 2) c := dist_nonneg
  nlinarith
private lemma g2_flip (e : Fin 3 → E3) (he : Orthonormal ℝ e) :
    Orthonormal ℝ (fun i : Fin 3 => if i = 2 then -e i else e i) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [orthonormal_iff_ite.mp he, he.norm_eq_one]

private lemma g2_upper_unique (n : ℕ) (c : Fin n → E3) (hc : Function.Injective c)
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      (∀ i, (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1) →
      ∀ i j, inner ℝ (e 2) (c i) + √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 -
        (p.2 - inner ℝ (e 1) (c i)) ^ 2) = inner ℝ (e 2) (c j) +
          √(1 - (p.1 - inner ℝ (e 0) (c j)) ^ 2 - (p.2 - inner ℝ (e 1) (c j)) ^ 2) → i = j := by
  classical
  have hpair (i j : Fin n) : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      (∀ i, (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1) →
      inner ℝ (e 2) (c i) + √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 -
        (p.2 - inner ℝ (e 1) (c i)) ^ 2) = inner ℝ (e 2) (c j) +
          √(1 - (p.1 - inner ℝ (e 0) (c j)) ^ 2 - (p.2 - inner ℝ (e 1) (c j)) ^ 2) → i = j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ _ _ => hij
    · have ht := SolidGeom.projected_sphere_tie_null (c i) (c j) (fun h => hij (hc h)) e he
      dsimp only at ht
      have hn := measure_eq_zero_iff_ae_notMem.mp ht
      filter_upwards [hn] with p hp
      intro hD heq
      exfalso
      apply hp
      refine ⟨hD i, ?_⟩
      rw [heq]
      exact g2_graph_mem (c j) e he p (hD j)
  have hall := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpair i))
  filter_upwards [hall] with p hp
  intro hD i j heq
  exact hp i j hD heq

theorem proof_SolidGeom_ae_ballInter_slice_endpoint_unique (n : ℕ) (c : Fin n → E3)
    (hc : Function.Injective c) (e : Fin 3 → E3) (he : Orthonormal ℝ e) :
    let D : Set (ℝ × ℝ) := {p | ∀ i, (p.1 - inner ℝ (e 0) (c i)) ^ 2 +
      (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
    let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ D →
      (∀ i j, l i p = l j p → i = j) ∧ (∀ i j, u i p = u j p → i = j) := by
  dsimp only
  have hu := g2_upper_unique n c hc e he
  have hl := g2_upper_unique n c hc
    (fun i : Fin 3 => if i = 2 then -e i else e i) (g2_flip e he)
  simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    ↓reduceIte, inner_neg_left] at hl
  filter_upwards [hu, hl] with p hup hlp
  intro hp
  constructor
  · intro i j hij
    apply hlp hp i j
    linarith
  · exact hup hp
