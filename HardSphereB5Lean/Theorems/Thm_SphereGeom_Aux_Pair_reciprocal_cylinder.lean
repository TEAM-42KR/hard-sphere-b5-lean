import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_reciprocal_cylinder
import HardSphereB5Lean.Definitions.Def_SphereGeom_Aux_Pair_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.reciprocal_cylinder :
    ∀ (w α ψ : ℝ) (hw : w^2 < 1), SphereGeom.Aux.Pair.reciprocal (SphereGeom.Aux.Pair.cylinder w α) ψ =
      SphereGeom.Aux.Pair.fiber w ψ α :=
  @proof_SphereGeom_Aux_Pair_reciprocal_cylinder
