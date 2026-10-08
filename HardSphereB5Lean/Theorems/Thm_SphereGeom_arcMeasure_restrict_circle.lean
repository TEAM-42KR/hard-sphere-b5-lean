import HardSphereB5Lean.Proofs.Proof_SphereGeom_arcMeasure_restrict_circle
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.arcMeasure_restrict_circle :
    ∀ (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ)
    (hr : 0 < r) (a b : ℝ) (hab : a ≤ b) (hb : b - a ≤ 2 * Real.pi), arcMeasure.restrict (circlePt c (e 0) (e 1) r '' Set.Icc a b) =
      ENNReal.ofReal r • (volume.restrict (Set.Icc a b)).map (circlePt c (e 0) (e 1) r) :=
  @proof_SphereGeom_arcMeasure_restrict_circle
