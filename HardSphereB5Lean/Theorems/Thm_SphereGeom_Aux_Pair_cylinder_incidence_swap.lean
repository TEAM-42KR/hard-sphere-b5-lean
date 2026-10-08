import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_cylinder_incidence_swap
import HardSphereB5Lean.Definitions.Def_SphereGeom_Aux_Pair_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.cylinder_incidence_swap :
    ∀ (H : E3 → E3 → ENNReal) (hH : Measurable (Function.uncurry H)), (∫⁻ z in Set.Icc (-1 : ℝ) 1, ∫⁻ φ in Set.Ico 0 (2 * Real.pi), ∫⁻ t in Set.Ico 0 (2 * Real.pi),
      H (SphereGeom.Aux.Pair.cylinder z φ) (SphereGeom.Aux.Pair.fiber z φ t)) =
    (∫⁻ z in Set.Icc (-1 : ℝ) 1, ∫⁻ φ in Set.Ico 0 (2 * Real.pi), ∫⁻ t in Set.Ico 0 (2 * Real.pi),
      H (SphereGeom.Aux.Pair.fiber z φ t) (SphereGeom.Aux.Pair.cylinder z φ)) :=
  @proof_SphereGeom_Aux_Pair_cylinder_incidence_swap
