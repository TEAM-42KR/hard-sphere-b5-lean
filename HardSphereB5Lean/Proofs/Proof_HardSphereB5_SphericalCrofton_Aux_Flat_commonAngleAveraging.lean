import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

theorem proof_HardSphereB5_SphericalCrofton_Aux_Flat_commonAngleAveraging
    (T : ℝ) (hT : 0 < T) (Q : ℝ × ℝ → ℝ)
    (hQ : Integrable Q ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))))
    (hper : Function.Periodic (fun χ : ℝ => Q (0, χ)) T)
    (hdiag : ∀ α β t : ℝ, Q (α + t, β + t) = Q (α, β)) :
    IntegrableOn (fun χ : ℝ => Q (0, χ)) (Ioc (-(T / 2)) (T / 2)) ∧
      (∫ p, Q p ∂((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T)))) =
        T * ∫ χ in Ioc (-(T / 2)) (T / 2), Q (0, χ) := by
  have hvol : volume (Ioc (0 : ℝ) T) ≠ 0 := by
    simpa only [Real.volume_Ioc, sub_zero, ENNReal.ofReal_ne_zero_iff] using hT
  obtain ⟨a, ha_mem, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol hQ.prod_right_ae
  have ha_int : IntervalIntegrable (fun y : ℝ => Q (a, y)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2 ha
  have htranslate : (fun y : ℝ => Q (a, y + a)) = (fun y : ℝ => Q (0, y)) := by
    funext y
    simpa only [zero_add] using hdiag 0 y a
  have hbase : IntervalIntegrable (fun y : ℝ => Q (0, y)) volume (-a) (-a + T) := by
    have h := ha_int.comp_add_right a
    rw [htranslate] at h
    convert h using 1 <;> ring
  have hcenter : IntervalIntegrable (fun y : ℝ => Q (0, y)) volume (-(T / 2)) (T / 2) :=
    hper.intervalIntegrable hT.ne' hbase _ _
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 hcenter, ?_⟩
  have hrep (x y : ℝ) : Q (x, y) = Q (0, y - x) := by
    have h := hdiag x y (-x)
    simpa only [add_neg_cancel, sub_eq_add_neg] using h.symm
  have hinner (x : ℝ) :
      (∫ y in Ioc 0 T, Q (x, y)) = ∫ y in Ioc (-(T / 2)) (T / 2), Q (0, y) := by
    rw [← intervalIntegral.integral_of_le hT.le]
    rw [show (fun y : ℝ => Q (x, y)) = (fun y : ℝ => Q (0, y - x)) from funext (hrep x)]
    rw [intervalIntegral.integral_comp_sub_right (fun y : ℝ => Q (0, y)) x]
    have hperiod := hper.intervalIntegral_add_eq (-x) (-(T / 2))
    have hleft : 0 - x = -x := by ring
    have hright : T - x = -x + T := by ring
    have hmid : -(T / 2) + T = T / 2 := by ring
    rw [hleft, hright, hperiod, hmid]
    exact intervalIntegral.integral_of_le (by linarith)
  rw [MeasureTheory.integral_prod Q hQ]
  simp_rw [hinner]
  simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal hT.le]
