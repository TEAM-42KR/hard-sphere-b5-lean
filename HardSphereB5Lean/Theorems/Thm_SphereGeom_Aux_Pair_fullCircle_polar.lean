import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_fullCircle_polar
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.fullCircle_polar :
    ∀ (c d u : E3) (hcd : Orthonormal ℝ ![c,d,u])
    (f : E3 → ENNReal) (hf : Measurable f), (∫⁻ t in Set.Ioc 0 (2*Real.pi), ∫⁻ s in Set.Ioc 0 (2*Real.pi),
      f (Real.cos s • u + Real.sin s • (-Real.sin t • c + Real.cos t • d)) *
        ENNReal.ofReal |Real.sin s|) = 2 * ∫⁻ v, f v ∂dOmega :=
  @proof_SphereGeom_Aux_Pair_fullCircle_polar
