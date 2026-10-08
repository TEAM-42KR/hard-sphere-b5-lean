import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_halfCircle_lintegral
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.halfCircle_lintegral :
    ∀ (u k : E3) (f : E3 → ENNReal) (hf : Measurable f), (∫⁻ w in Set.Icc (-1 : ℝ) 1, f (w • u + Real.sqrt (1-w^2) • k)) =
    ∫⁻ s in Set.Ioc 0 Real.pi, ENNReal.ofReal (Real.sin s) * f (Real.cos s • u + Real.sin s • k) :=
  @proof_SphereGeom_Aux_Pair_halfCircle_lintegral
