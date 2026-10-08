import HardSphereB5Lean.Proofs.Proof_SolidGeom_moment_sum_ballInter_inj
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.moment_sum_ballInter_inj :
    ∀ (n : ℕ) (c : Fin n → E3) (hc : Function.Injective c)
    (hK : (interior (⋂ i, Metric.closedBall (c i) 1)).Nonempty), ∑ i, ∫ x in ⋂ j, Metric.closedBall (c j) 1, (x - c i) ∂(sphereMeasure (c i)) = 0 :=
  @proof_SolidGeom_moment_sum_ballInter_inj
