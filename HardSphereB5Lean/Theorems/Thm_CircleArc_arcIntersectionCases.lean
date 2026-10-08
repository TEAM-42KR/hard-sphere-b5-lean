import HardSphereB5Lean.Proofs.Proof_CircleArc_arcIntersectionCases
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem CircleArc.arcIntersectionCases :
    ∀ (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (βa βb φ : ℝ) (ha0 : 0 < βa) (haπ : βa < Real.pi) (hb0 : 0 < βb) (hbπ : βb < Real.pi) (hφ0 : 0 < φ) (hφπ : φ < Real.pi), ((|βa - βb| < φ) → (φ < βa + βb) → (βa + βb + φ < 2 * Real.pi) →
      ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩ (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb)) = circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) βa ∧
        arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩ (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb))) = ENNReal.ofReal (r * (βa + βb - φ)))) ∧
    ((φ + βb ≤ βa) →
      ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩ (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb)) = circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb) ∧
        arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩ (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb))) = ENNReal.ofReal (2 * r * βb))) ∧
    ((βa + βb < φ) →
      ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩ (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb)) = ∅ ∧
        arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩ (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb))) = 0)) :=
  @proof_CircleArc_arcIntersectionCases
