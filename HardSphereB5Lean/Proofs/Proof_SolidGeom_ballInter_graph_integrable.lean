import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped BigOperators Classical

theorem proof_SolidGeom_ballInter_graph_integrable (n : ℕ) (c : Fin n → E3)
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) (a b : ℝ) :
    let K : Set E3 := ⋂ i, Metric.closedBall (c i) 1
    let D : Fin n → Set (ℝ × ℝ) := fun i => {p |
      (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
    let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
      √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let X : (ℝ × ℝ) → ℝ → E3 := fun p z => p.1 • e 0 + p.2 • e 1 + z • e 2
    ∀ i,
      IntegrableOn (fun p => if X p (u i p) ∈ K then a + b * u i p else 0) (D i) ∧
      IntegrableOn (fun p => if X p (l i p) ∈ K then a + b * l i p else 0) (D i) := by
  classical
  dsimp only
  let K : Set E3 := ⋂ i, Metric.closedBall (c i) 1
  let D : Fin n → Set (ℝ × ℝ) := fun i => {p |
    (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
  let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
    √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
  let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
    √(1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
  let X : (ℝ × ℝ) → ℝ → E3 := fun p z => p.1 • e 0 + p.2 • e 1 + z • e 2
  change ∀ i,
    IntegrableOn (fun p => if X p (u i p) ∈ K then a + b * u i p else 0) (D i) ∧
    IntegrableOn (fun p => if X p (l i p) ∈ K then a + b * l i p else 0) (D i)
  have hK : MeasurableSet K := MeasurableSet.iInter (fun j => Metric.isClosed_closedBall.measurableSet)
  intro i
  let x₀ : ℝ := inner ℝ (e 0) (c i)
  let y₀ : ℝ := inner ℝ (e 1) (c i)
  let R : Set (ℝ × ℝ) := Set.Icc (x₀ - 1) (x₀ + 1) ×ˢ Set.Icc (y₀ - 1) (y₀ + 1)
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hDR : D i ⊆ R := by
    intro p hp
    change (p.1 - x₀) ^ 2 + (p.2 - y₀) ^ 2 < 1 at hp
    change (x₀ - 1 ≤ p.1 ∧ p.1 ≤ x₀ + 1) ∧ (y₀ - 1 ≤ p.2 ∧ p.2 ≤ y₀ + 1)
    have hx : (p.1 - x₀) ^ 2 < 1 := by nlinarith [sq_nonneg (p.2 - y₀)]
    have hy : (p.2 - y₀) ^ 2 < 1 := by nlinarith [sq_nonneg (p.1 - x₀)]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      nlinarith [sq_nonneg (p.1 - x₀ + 1), sq_nonneg (p.1 - x₀ - 1),
        sq_nonneg (p.2 - y₀ + 1), sq_nonneg (p.2 - y₀ - 1)]
  have hFu : Continuous (fun p => a + b * u i p) := by fun_prop
  have hFl : Continuous (fun p => a + b * l i p) := by fun_prop
  have hXu : Continuous (fun p => X p (u i p)) := by fun_prop
  have hXl : Continuous (fun p => X p (l i p)) := by fun_prop
  have hIU : IntegrableOn (fun p => a + b * u i p) (D i) (volume : Measure (ℝ × ℝ)) :=
    (hFu.continuousOn.integrableOn_compact hR).mono_set hDR
  have hIL : IntegrableOn (fun p => a + b * l i p) (D i) (volume : Measure (ℝ × ℝ)) :=
    (hFl.continuousOn.integrableOn_compact hR).mono_set hDR
  constructor
  · change IntegrableOn (((fun p => X p (u i p)) ⁻¹' K).indicator
      (fun p => a + b * u i p)) (D i) (volume : Measure (ℝ × ℝ))
    exact hIU.indicator (hK.preimage hXu.measurable)
  · change IntegrableOn (((fun p => X p (l i p)) ⁻¹' K).indicator
      (fun p => a + b * l i p)) (D i) (volume : Measure (ℝ × ℝ))
    exact hIL.indicator (hK.preimage hXl.measurable)

#print axioms proof_SolidGeom_ballInter_graph_integrable
