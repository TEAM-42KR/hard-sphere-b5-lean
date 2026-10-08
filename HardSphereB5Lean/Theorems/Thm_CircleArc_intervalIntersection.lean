import HardSphereB5Lean.Proofs.Proof_CircleArc_intervalIntersection
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem CircleArc.intervalIntersection :
    ∀ (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (a b d f : ℝ) (hspan : max b f - min a d < 2 * Real.pi), (circlePt c (e 0) (e 1) r '' Set.Icc a b) ∩ (circlePt c (e 0) (e 1) r '' Set.Icc d f) = circlePt c (e 0) (e 1) r '' Set.Icc (max a d) (min b f) ∧
    arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc a b) ∩ (circlePt c (e 0) (e 1) r '' Set.Icc d f)) = ENNReal.ofReal (r * (min b f - max a d)) :=
  @proof_CircleArc_intervalIntersection
