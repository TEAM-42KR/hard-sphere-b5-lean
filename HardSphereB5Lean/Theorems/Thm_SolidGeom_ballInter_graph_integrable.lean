import HardSphereB5Lean.Proofs.Proof_SolidGeom_ballInter_graph_integrable
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped BigOperators Classical

theorem SolidGeom.ballInter_graph_integrable :
    ∀ (n : ℕ) (c : Fin n → E3)
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) (a b : ℝ),
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
      IntegrableOn (fun p => if X p (l i p) ∈ K then a + b * l i p else 0) (D i) :=
  @proof_SolidGeom_ballInter_graph_integrable
