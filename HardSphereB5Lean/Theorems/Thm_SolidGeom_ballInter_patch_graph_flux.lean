import HardSphereB5Lean.Proofs.Proof_SolidGeom_ballInter_patch_graph_flux
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped Classical

theorem SolidGeom.ballInter_patch_graph_flux :
    ∀ (n : ℕ) (c : Fin n → E3)
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) (a b : ℝ),
    let K : Set E3 := ⋂ j : Fin n, Metric.closedBall (c j) 1
    let D : Fin n → Set (ℝ × ℝ) := fun i =>
      {p | (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
    let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
      Real.sqrt (1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
      Real.sqrt (1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let X : ℝ × ℝ → ℝ → E3 := fun p z => p.1 • e 0 + p.2 • e 1 + z • e 2
    (∑ i : Fin n, ∫ x in K, (a + b * inner ℝ (e 2) x) *
      inner ℝ (e 2) (x - c i) ∂sphereMeasure (c i)) =
    (∑ i : Fin n, ∫ p in D i, if X p (u i p) ∈ K then a + b * u i p else 0) -
    (∑ i : Fin n, ∫ p in D i, if X p (l i p) ∈ K then a + b * l i p else 0) :=
  @proof_SolidGeom_ballInter_patch_graph_flux
