import HardSphereB5Lean.Proofs.Proof_CircleArc_pair_circle_on_spheres
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom
open scoped RealInnerProductSpace

theorem CircleArc.pair_circle_on_spheres :
    ∀ (a b : E3) (e : Fin 2 → E3)
    (he : Orthonormal ℝ e) (hperp : ∀ i, inner ℝ (b - a) (e i) = 0)
    (hd : dist a b < 2) (t : ℝ), circlePt ((1 / 2 : ℝ) • (a + b)) (e 0) (e 1)
      (Real.sqrt (1 - dist a b ^ 2 / 4)) t ∈ Metric.sphere a 1 ∩ Metric.sphere b 1 :=
  @proof_CircleArc_pair_circle_on_spheres
