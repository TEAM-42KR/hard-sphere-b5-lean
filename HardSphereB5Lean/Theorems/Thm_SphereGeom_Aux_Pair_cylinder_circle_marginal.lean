import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_cylinder_circle_marginal
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.cylinder_circle_marginal :
    ∀ (f : E3 → ENNReal) (hf : Measurable f), (∫⁻ z in Set.Icc (-1 : ℝ) 1, ∫⁻ φ in Set.Ico 0 (2 * Real.pi),
      ∫⁻ t in Set.Ico 0 (2 * Real.pi),
        f (circlePt 0 (WithLp.toLp 2 ![-Real.sin φ, Real.cos φ, 0])
          (WithLp.toLp 2 ![-z * Real.cos φ, -z * Real.sin φ, Real.sqrt (1-z^2)]) 1 t)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ u, f u ∂dOmega :=
  @proof_SphereGeom_Aux_Pair_cylinder_circle_marginal
