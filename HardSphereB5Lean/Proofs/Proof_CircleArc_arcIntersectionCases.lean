import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
import HardSphereB5Lean.Theorems.Thm_CircleArc_intervalIntersection
set_option autoImplicit false
open MeasureTheory SphereGeom CircleArc
theorem proof_CircleArc_arcIntersectionCases (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e)
    (r : ℝ) (hr : 0 < r) (βa βb φ : ℝ)
    (ha0 : 0 < βa) (haπ : βa < Real.pi)
    (hb0 : 0 < βb) (hbπ : βb < Real.pi)
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    ((|βa - βb| < φ) → (φ < βa + βb) →
      (βa + βb + φ < 2 * Real.pi) →
      ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩
          (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb)) =
        circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) βa ∧
      arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩
          (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb))) =
        ENNReal.ofReal (r * (βa + βb - φ)))) ∧
    ((φ + βb ≤ βa) →
      ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩
          (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb)) =
        circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb) ∧
      arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩
          (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb))) =
        ENNReal.ofReal (2 * r * βb))) ∧
    ((βa + βb < φ) →
      ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩
          (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb)) = ∅ ∧
      arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩
          (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb))) = 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hinner hmeet hnowrap
    rcases abs_lt.mp hinner with ⟨hdiffL, hdiffR⟩
    have hl : -βa ≤ φ - βb := by linarith
    have hu : βa ≤ φ + βb := by linarith
    have hspan : max βa (φ + βb) - min (-βa) (φ - βb) < 2 * Real.pi := by
      rw [max_eq_right hu, min_eq_left hl]
      linarith
    have h := intervalIntersection c e he r hr (-βa) βa (φ - βb) (φ + βb) hspan
    simp only [max_eq_right hl, min_eq_left hu] at h
    refine ⟨h.1, ?_⟩
    rw [h.2]
    congr 1
    ring
  · intro hcontain
    have hsub : Set.Icc (φ - βb) (φ + βb) ⊆ Set.Icc (-βa) βa := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hsets : (circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb)) =
        circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb) :=
      Set.inter_eq_right.mpr (Set.image_mono hsub)
    have hmeasure := SphereGeom.arcMeasure_circle_arc c e he r hr
      (φ - βb) (φ + βb) (by linarith) (by linarith)
    refine ⟨hsets, ?_⟩
    rw [hsets, hmeasure]
    congr 1
    ring
  · intro hsep
    have hl : -βa ≤ φ - βb := by linarith
    have hu : βa ≤ φ + βb := by linarith
    have hspan : max βa (φ + βb) - min (-βa) (φ - βb) < 2 * Real.pi := by
      rw [max_eq_right hu, min_eq_left hl]
      linarith
    have h := intervalIntersection c e he r hr (-βa) βa (φ - βb) (φ + βb) hspan
    simp only [max_eq_right hl, min_eq_left hu] at h
    have hempty : Set.Icc (φ - βb) βa = ∅ :=
      Set.Icc_eq_empty_of_lt (by linarith)
    have hsets : (circlePt c (e 0) (e 1) r '' Set.Icc (-βa) βa) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc (φ - βb) (φ + βb)) = ∅ := by
      simpa only [hempty, Set.image_empty] using h.1
    refine ⟨hsets, ?_⟩
    rw [hsets, measure_empty]
