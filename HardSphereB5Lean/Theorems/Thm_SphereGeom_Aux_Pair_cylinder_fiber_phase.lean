import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_cylinder_fiber_phase
import HardSphereB5Lean.Definitions.Def_SphereGeom_Aux_Pair_cylinder
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.cylinder_fiber_phase :
    ∀ (z φ t : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1), SphereGeom.Aux.Pair.fiber z φ t = SphereGeom.Aux.Pair.cylinder
      (Real.sqrt (1-z^2) * Real.sin t) (φ + (⟨-z * Real.sin t, Real.cos t⟩ : ℂ).arg) :=
  @proof_SphereGeom_Aux_Pair_cylinder_fiber_phase
