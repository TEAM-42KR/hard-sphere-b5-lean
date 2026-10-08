import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_contact_small_circle_subset
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SphereGeom.Aux.contact_small_circle_subset :
    ∀ (q : E3) (hbound : ‖q‖ ≤ 1)
(h0 : q ≠ 0) (E : Fin 3 → E3) (hE : Orthonormal ℝ E) (hn : E 2 = ‖q‖⁻¹ • (-q)), {u : E3 | ‖u‖ = 1 ∧ ‖q + u‖ = 1} ⊆
circlePt ((-(1 / 2 : ℝ)) • q) (E 0) (E 1) (Real.sqrt (1 - ‖q‖ ^ 2 / 4)) ''
Set.Icc (0 : ℝ) (2 * π) :=
  @proof_SphereGeom_Aux_contact_small_circle_subset
