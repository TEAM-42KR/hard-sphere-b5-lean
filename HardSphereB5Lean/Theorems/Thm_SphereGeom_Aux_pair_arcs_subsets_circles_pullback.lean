import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_pair_arcs_subsets_circles_pullback
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped Classical

theorem SphereGeom.Aux.pair_arcs_subsets_circles_pullback :
    ∀ (cA cB : E3) (EA EB : Fin 2 → E3) (hEA : Orthonormal ℝ EA) (hEB : Orthonormal ℝ EB)
(rA rB : ℝ) (hrA : 0 < rA) (hrB : 0 < rB)
(A B : Set E3) (hA : MeasurableSet A) (hB : MeasurableSet B)
(hsubA : A ⊆ circlePt cA (EA 0) (EA 1) rA '' Set.Icc (0 : ℝ) (2 * π))
(hsubB : B ⊆ circlePt cB (EB 0) (EB 1) rB '' Set.Icc (0 : ℝ) (2 * π))
(g : E3 × E3 → ℝ) (hg : Measurable g), (∫ u in A, ∫ v in B, g (u,v) ∂arcMeasure ∂arcMeasure) =
rA * rB * ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π),
if circlePt cA (EA 0) (EA 1) rA t ∈ A ∧ circlePt cB (EB 0) (EB 1) rB s ∈ B
then g (circlePt cA (EA 0) (EA 1) rA t, circlePt cB (EB 0) (EB 1) rB s) else 0 :=
  @proof_SphereGeom_Aux_pair_arcs_subsets_circles_pullback
