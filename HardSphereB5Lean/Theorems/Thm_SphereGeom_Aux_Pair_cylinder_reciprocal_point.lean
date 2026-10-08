import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_cylinder_reciprocal_point
import HardSphereB5Lean.Definitions.Def_SphereGeom_Aux_Pair_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.cylinder_reciprocal_point :
    ∀ (z t ψ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hw : (Real.sqrt (1-z^2) * Real.sin t)^2 < 1), SphereGeom.Aux.Pair.cylinder z (ψ - (⟨-z * Real.sin t, Real.cos t⟩ : ℂ).arg) =
      SphereGeom.Aux.Pair.reciprocal (SphereGeom.Aux.Pair.meridian z t) ψ :=
  @proof_SphereGeom_Aux_Pair_cylinder_reciprocal_point
