import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_periodic_lintegral_translate
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.periodic_lintegral_translate :
    ∀ (f : ℝ → ENNReal) (T : ℝ) (hT : 0 < T)
    (hf : Function.Periodic f T) (a s : ℝ), (∫⁻ t in Set.Ioc a (a + T), f (t + s)) = ∫⁻ t in Set.Ioc a (a + T), f t :=
  @proof_SphereGeom_Aux_Pair_periodic_lintegral_translate
