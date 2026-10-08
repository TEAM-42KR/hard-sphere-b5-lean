import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_pair_arc_subset_circle_pullback
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped Classical

theorem SphereGeom.Aux.pair_arc_subset_circle_pullback :
    ∀ (c : E3) (E : Fin 2 → E3) (hE : Orthonormal ℝ E) (r : ℝ) (hr : 0 < r) (A : Set E3) (hA : MeasurableSet A) (hsub : A ⊆ circlePt c (E 0) (E 1) r '' Set.Icc (0 : ℝ) (2 * π)) (g : E3 × E3 → ℝ) (hg : Measurable g), (∫ u in A, ∫ v in A, g (u, v) ∂arcMeasure ∂arcMeasure) = r ^ 2 * ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π), if circlePt c (E 0) (E 1) r t ∈ A ∧ circlePt c (E 0) (E 1) r s ∈ A then g (circlePt c (E 0) (E 1) r t, circlePt c (E 0) (E 1) r s) else 0 :=
  @proof_SphereGeom_Aux_pair_arc_subset_circle_pullback
