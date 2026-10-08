import HardSphereB5Lean.Proofs.Proof_SolidGeom_ballInter_affine_slice_flux
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.ballInter_affine_slice_flux :
    ∀ (n : ℕ) (c : Fin n → E3) (hc : Function.Injective c)
    (hK : (interior (⋂ i, Metric.closedBall (c i) 1)).Nonempty)
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) (a b : ℝ), ∑ i, ∫ x in ⋂ j, Metric.closedBall (c j) 1,
      (a + b * inner ℝ (e 2) x) * inner ℝ (e 2) (x - c i) ∂(sphereMeasure (c i)) =
      b * (volume (⋂ i, Metric.closedBall (c i) 1)).toReal :=
  @proof_SolidGeom_ballInter_affine_slice_flux
