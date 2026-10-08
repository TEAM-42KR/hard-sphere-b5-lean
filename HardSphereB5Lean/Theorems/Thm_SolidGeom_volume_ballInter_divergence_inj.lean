import HardSphereB5Lean.Proofs.Proof_SolidGeom_volume_ballInter_divergence_inj
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.volume_ballInter_divergence_inj :
    ∀ (n : ℕ) (c : Fin n → E3) (hc : Function.Injective c)
    (hK : (interior (⋂ i, Metric.closedBall (c i) 1)).Nonempty), 3 * (volume (⋂ i, Metric.closedBall (c i) 1)).toReal =
      ∑ i, ((sphereMeasure (c i) (⋂ j, Metric.closedBall (c j) 1)).toReal
        + inner ℝ (c i) (∫ x in ⋂ j, Metric.closedBall (c j) 1, (x - c i) ∂(sphereMeasure (c i)))) :=
  @proof_SolidGeom_volume_ballInter_divergence_inj
