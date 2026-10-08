import HardSphereB5Lean.Theorems.Thm_SphereGeom_twoBallSurface_capReduction
import HardSphereB5Lean.Theorems.Thm_SphereGeom_pair_normalized_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_cap_positive_smul
import HardSphereB5Lean.Theorems.Thm_SphereGeom_twoCap_area_slice
import HardSphereB5Lean.Theorems.Thm_SolidGeom_Q_positive_gram
import HardSphereB5Lean.Theorems.Thm_SolidGeom_twoCap_rhs_normalization
set_option autoImplicit false

open SphereGeom MeasureTheory Real
set_option maxHeartbeats 500000

theorem proof_SolidGeom_area_two_cap_slice (x y z : E3)
    (hQ : 0 < 4 * dist x y ^ 2 * dist x z ^ 2 - (dist x y ^ 2 + dist x z ^ 2 - dist y z ^ 2) ^ 2
      - dist x y ^ 2 * dist x z ^ 2 * dist y z ^ 2) :
    let a := dist x y ^ 2
    let b := dist x z ^ 2
    let c := dist y z ^ 2
    let k := Real.sqrt a / 2
    let l := Real.sqrt b / 2
    let alpha := Real.arccos ((a + b - c) / (2 * Real.sqrt a * Real.sqrt b))
    let H := min (Real.sqrt (1 - k ^ 2)) (Real.sqrt (1 - l ^ 2))
    let f := fun t : ℝ => Real.arccos (k / Real.sqrt (1 - t ^ 2))
    let g := fun t : ℝ => Real.arccos (l / Real.sqrt (1 - t ^ 2))
    (sphereMeasure x (Metric.closedBall y 1 ∩ Metric.closedBall z 1)).toReal =
      2 * (∫ t in (0 : ℝ)..H, max 0 (min (2 * f t) (min (2 * g t) (f t + g t - alpha))))  := by
  let a := dist x y ^ 2
  let b := dist x z ^ 2
  let c := dist y z ^ 2
  let k := sqrt a / 2
  let l := sqrt b / 2
  let alpha := arccos ((a + b - c) / (2 * sqrt a * sqrt b))
  let H := min (sqrt (1 - k ^ 2)) (sqrt (1 - l ^ 2))
  let f := fun t : ℝ => arccos (k / sqrt (1 - t ^ 2))
  let g := fun t : ℝ => arccos (l / sqrt (1 - t ^ 2))
  change (sphereMeasure x (Metric.closedBall y 1 ∩ Metric.closedBall z 1)).toReal =
    2 * (∫ t in (0 : ℝ)..H, max 0 (min (2 * f t) (min (2 * g t) (f t + g t - alpha))))
  have hQa : 0 < 4 * a * b - (a + b - c) ^ 2 - a * b * c := hQ
  have hnorm := SolidGeom.twoCap_rhs_normalization a b c
    (sq_nonneg (dist x y)) (sq_nonneg (dist x z)) (sq_nonneg (dist y z)) hQa
  rcases hnorm.1 with ⟨hk0, hk1, hl0, hl1, halpha0, halpha1, hD⟩
  change 0 < k at hk0
  change k < 1 at hk1
  change 0 < l at hl0
  change l < 1 at hl1
  change 0 < alpha at halpha0
  change alpha < π at halpha1
  have hvdist : dist x y = ‖y - x‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hwdist : dist x z = ‖z - x‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hsqa : sqrt a = ‖y - x‖ := by
    dsimp only [a]
    rw [sqrt_sq (show 0 ≤ dist x y from dist_nonneg), hvdist]
  have hsqb : sqrt b = ‖z - x‖ := by
    dsimp only [b]
    rw [sqrt_sq (show 0 ≤ dist x z from dist_nonneg), hwdist]
  have hvpos : 0 < ‖y - x‖ := by
    have hp : 0 < sqrt a / 2 := hk0
    rw [hsqa] at hp
    linarith only [hp]
  have hwpos : 0 < ‖z - x‖ := by
    have hp : 0 < sqrt b / 2 := hl0
    rw [hsqb] at hp
    linarith only [hp]
  have hdiff : y - z = (y - x) - (z - x) := by abel
  have hcNorm : dist y z ^ 2 = ‖y - x‖ ^ 2 + ‖z - x‖ ^ 2 -
      2 * inner ℝ (y - x) (z - x) := by
    rw [dist_eq_norm, hdiff, norm_sub_sq_real]
    ring
  have hinner : inner ℝ (y - x) (z - x) = (a + b - c) / 2 := by
    rw [← hvdist, ← hwdist] at hcNorm
    change c = a + b - 2 * inner ℝ (y - x) (z - x) at hcNorm
    linarith only [hcNorm]
  have hangle : arccos (inner ℝ (y - x) (z - x) / (‖y - x‖ * ‖z - x‖)) = alpha := by
    change arccos (inner ℝ (y - x) (z - x) / (‖y - x‖ * ‖z - x‖)) =
      arccos ((a + b - c) / (2 * sqrt a * sqrt b))
    rw [hinner, ← hsqa, ← hsqb]
    simp only [div_div, mul_assoc]
  obtain ⟨e, he, hve, hwe⟩ := SphereGeom.pair_normalized_frame (y - x) (z - x)
    (SolidGeom.Q_positive_gram x y z hQ)
  rw [hangle] at hwe
  have hkScale : ‖y - x‖ * k = ‖y - x‖ ^ 2 / 2 := by
    change ‖y - x‖ * (sqrt a / 2) = ‖y - x‖ ^ 2 / 2
    rw [hsqa]
    ring
  have hlScale : ‖z - x‖ * l = ‖z - x‖ ^ 2 / 2 := by
    change ‖z - x‖ * (sqrt b / 2) = ‖z - x‖ ^ 2 / 2
    rw [hsqb]
    ring
  have hcapv : cap (y - x) (‖y - x‖ ^ 2 / 2) = cap (e 0) k := by
    calc
      cap (y - x) (‖y - x‖ ^ 2 / 2) = cap (‖y - x‖ • e 0) (‖y - x‖ * k) :=
        congrArg₂ cap hve hkScale.symm
      _ = cap (e 0) k := SphereGeom.cap_positive_smul (e 0) k ‖y - x‖ hvpos
  have hcapw : cap (z - x) (‖z - x‖ ^ 2 / 2) = cap (cos alpha • e 0 + sin alpha • e 1) l := by
    calc
      cap (z - x) (‖z - x‖ ^ 2 / 2) =
          cap (‖z - x‖ • (cos alpha • e 0 + sin alpha • e 1)) (‖z - x‖ * l) :=
        congrArg₂ cap hwe hlScale.symm
      _ = cap (cos alpha • e 0 + sin alpha • e 1) l :=
        SphereGeom.cap_positive_smul (cos alpha • e 0 + sin alpha • e 1) l ‖z - x‖ hwpos
  calc
    (sphereMeasure x (Metric.closedBall y 1 ∩ Metric.closedBall z 1)).toReal =
        (dOmega (cap (y - x) (‖y - x‖ ^ 2 / 2) ∩ cap (z - x) (‖z - x‖ ^ 2 / 2))).toReal :=
      congrArg ENNReal.toReal (SphereGeom.twoBallSurface_capReduction x y z).1
    _ = (dOmega (cap (e 0) k ∩ cap (cos alpha • e 0 + sin alpha • e 1) l)).toReal := by
      rw [hcapv, hcapw]
    _ = 2 * (∫ t in (0 : ℝ)..H, max 0 (min (2 * f t) (min (2 * g t) (f t + g t - alpha)))) :=
      SphereGeom.twoCap_area_slice e he k l alpha hk0 hk1 hl0 hl1 halpha0 halpha1
