import Mathlib
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_angleSheetInverseMeasure
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Flat_bothAngleSheetsMeasure (a b : ℝ) (hb : 0 < b) :
    let μ := (volume.restrict (Set.Ioo (a - b) (a + b))).withDensity
      (fun s => ENNReal.ofReal (1 / Real.sqrt (b ^ 2 - (s - a) ^ 2)))
    μ.map (fun s => Real.arccos ((a - s) / b)) +
      μ.map (fun s => -Real.arccos ((a - s) / b)) =
      volume.restrict (Set.Ioo (-Real.pi) Real.pi) := by
  let μ := (volume.restrict (Set.Ioo (a - b) (a + b))).withDensity
    (fun s => ENNReal.ofReal (1 / Real.sqrt (b ^ 2 - (s - a) ^ 2)))
  let inv : ℝ → ℝ := fun s => Real.arccos ((a - s) / b)
  have hinv : Measurable inv := by unfold inv; fun_prop
  have hpos : μ.map inv = volume.restrict (Set.Ioo (0 : ℝ) Real.pi) :=
    HardSphereB5.SphericalCrofton.Aux.Flat.angleSheetInverseMeasure a b hb
  have hneg : μ.map (fun s => -inv s) = volume.restrict (Set.Ioo (-Real.pi) (0 : ℝ)) := by
    change μ.map (Neg.neg ∘ inv) = _
    rw [← Measure.map_map measurable_neg hinv, hpos]
    have hpre : Neg.neg ⁻¹' Set.Ioo (-Real.pi) (0 : ℝ) = Set.Ioo (0 : ℝ) Real.pi := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioo, neg_lt_zero]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [← hpre, ← Measure.restrict_map measurable_neg measurableSet_Ioo,
      Measure.map_neg_eq_self]
  have hsplit : (volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi) =
      volume.restrict (Set.Ioo (-Real.pi) 0) + volume.restrict (Set.Ioo 0 Real.pi) := by
    simp only [restrict_Ioo_eq_restrict_Ioc]
    rw [← Measure.restrict_union (Set.Ioc_disjoint_Ioc.mpr (by simp)) measurableSet_Ioc,
      Set.Ioc_union_Ioc_eq_Ioc (by linarith [Real.pi_pos]) Real.pi_pos.le]
  change μ.map inv + μ.map (fun s => -inv s) = _
  rw [hpos, hneg, hsplit, add_comm]
