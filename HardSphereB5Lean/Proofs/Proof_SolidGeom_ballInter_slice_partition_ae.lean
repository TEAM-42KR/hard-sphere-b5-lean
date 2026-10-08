import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SolidGeom_ae_ballInter_slice_endpoint_unique
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

private lemma g2_interval_sum {n : ℕ} (a b : Fin n → ℝ) (L U : ℝ) (i j : Fin n)
    (ha : ∀k, a k ≤ L) (hb : ∀k, U ≤ b k) (hi : a i = L) (hj : b j = U)
    (hau : ∀k m, a k = a m → k = m) (hbu : ∀k m, b k = b m → k = m) (F : ℝ → ℝ) :
    (∑k, if b k ∈ Set.Icc L U then F (b k) else 0) -
      (∑k, if a k ∈ Set.Icc L U then F (a k) else 0) =
        if L ≤ U then F U - F L else 0 := by
  classical
  by_cases hLU : L ≤ U
  · have hr (k : Fin n) : b k ∈ Set.Icc L U ↔ k = j := by
      constructor
      · intro h
        apply hbu k j
        rw [hj]
        exact le_antisymm h.2 (hb k)
      · rintro rfl
        simpa only [hj, Set.mem_Icc] using ⟨hLU, le_refl U⟩
    have hl (k : Fin n) : a k ∈ Set.Icc L U ↔ k = i := by
      constructor
      · intro h
        apply hau k i
        rw [hi]
        exact le_antisymm (ha k) h.1
      · rintro rfl
        simpa only [hi, Set.mem_Icc] using ⟨le_refl L, hLU⟩
    simp [hr, hl, hi, hj, hLU]
  · have hI : Set.Icc L U = ∅ := Set.Icc_eq_empty_of_lt (lt_of_not_ge hLU)
    simp [hI, hLU]

private theorem g2_vertical (n : ℕ) (c : Fin n → E3)
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) (p : ℝ × ℝ)
    (hp : ∀ i, (p.1 - inner ℝ (e 0) (c i)) ^ 2 +
      (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1) (z : ℝ) :
    p.1 • e 0 + p.2 • e 1 + z • e 2 ∈ (⋂ i, Metric.closedBall (c i) 1) ↔
      ∀ i, inner ℝ (e 2) (c i) - √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 -
        (p.2 - inner ℝ (e 1) (c i)) ^ 2) ≤ z ∧
        z ≤ inner ℝ (e 2) (c i) + √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 -
          (p.2 - inner ℝ (e 1) (c i)) ^ 2) := by
  simp only [Set.mem_iInter, Metric.mem_closedBall]
  apply forall_congr'
  intro i
  rw [← sq_le_sq₀ (dist_nonneg : 0 ≤ dist (p.1 • e 0 + p.2 • e 1 + z • e 2) (c i))
    zero_le_one, g2_cdist (c i) e he p z]
  have hm : 0 ≤ 1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 -
    (p.2 - inner ℝ (e 1) (c i)) ^ 2 := by linarith [hp i]
  have hs := sq_sqrt hm
  have hs0 := sqrt_nonneg (1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 -
    (p.2 - inner ℝ (e 1) (c i)) ^ 2)
  have heq : (p.1 - inner ℝ (e 0) (c i)) ^ 2 +
    (p.2 - inner ℝ (e 1) (c i)) ^ 2 + (z - inner ℝ (e 2) (c i)) ^ 2 ≤ 1 ^ 2 ↔
    (z - inner ℝ (e 2) (c i)) ^ 2 ≤
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2) ^ 2 := by
    constructor <;> intro hh <;> nlinarith
  rw [heq, sq_le_sq, abs_of_nonneg hs0, abs_le]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem proof_SolidGeom_ballInter_slice_partition_ae (n : ℕ) (hn : 0 < n) (c : Fin n → E3)
    (hc : Function.Injective c) (e : Fin 3 → E3) (he : Orthonormal ℝ e) :
    let D : Set (ℝ × ℝ) := {p | ∀ i, (p.1 - inner ℝ (e 0) (c i)) ^ 2 +
      (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
    let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ D → ∃ i j,
      (∀ k, l k p ≤ l i p ∧ u j p ≤ u k p) ∧
      (∀ z : ℝ, p.1 • e 0 + p.2 • e 1 + z • e 2 ∈
        (⋂ k, Metric.closedBall (c k) 1) ↔ z ∈ Set.Icc (l i p) (u j p)) ∧
      (∀ F : ℝ → ℝ,
        (∑ k, if u k p ∈ Set.Icc (l i p) (u j p) then F (u k p) else 0) -
          (∑ k, if l k p ∈ Set.Icc (l i p) (u j p) then F (l k p) else 0) =
            if l i p ≤ u j p then F (u j p) - F (l i p) else 0) := by
  classical
  dsimp only
  let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
    √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
  let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
    √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hunique := SolidGeom.ae_ballInter_slice_endpoint_unique n c hc e he
  dsimp only at hunique
  filter_upwards [hunique] with p hup
  intro hD
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun k => l k p) Finset.univ_nonempty
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image Finset.univ (fun k => u k p) Finset.univ_nonempty
  have hl (k : Fin n) : l k p ≤ l i p := hmax k (Finset.mem_univ k)
  have hu (k : Fin n) : u j p ≤ u k p := hmin k (Finset.mem_univ k)
  refine ⟨i, j, (fun k => ⟨hl k, hu k⟩), ?_, ?_⟩
  · intro z
    rw [g2_vertical n c e he p hD z]
    change (∀k, l k p ≤ z ∧ z ≤ u k p) ↔ z ∈ Set.Icc (l i p) (u j p)
    constructor
    · intro hz
      exact ⟨(hz i).1, (hz j).2⟩
    · intro hz k
      exact ⟨(hl k).trans hz.1, hz.2.trans (hu k)⟩
  · intro F
    exact g2_interval_sum (fun k => l k p) (fun k => u k p) (l i p) (u j p) i j
      hl hu rfl rfl (hup hD).1 (hup hD).2 F
