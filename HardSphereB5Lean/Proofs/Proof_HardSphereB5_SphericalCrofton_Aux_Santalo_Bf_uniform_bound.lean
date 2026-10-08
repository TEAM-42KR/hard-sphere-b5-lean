import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_isChart_exists
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_kernel_transport
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_measurable_kernels
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_inactive_cross_zero
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_bKernel_uniform_bound
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_Bf_uniform_bound (f : Kern) (D : Pt) (hD : D ∈ LamC) : ‖Bf f D‖ ≤ 16 * Real.pi ^ 2 := by
  by_cases hact : offAxis D ∧ Rc ‖D‖ ‖D - e‖ < 1
  · obtain ⟨C, hC⟩ := HardSphereB5.SphericalCrofton.Aux.MovingArc.isChart_exists D hD hact.1 hact.2
    change ‖∫ p in arcA D, ∫ q in arcB D, bKernel f D p q ∂arcMeasure ∂arcMeasure‖ ≤ _
    rw [kernel_transport D C hC (bKernel f D) (measurable_kernels f D).2]
    rcases hC with ⟨hEA, hEB, hrA, hrB, hTA, hTB, hTApi, hTBpi, hArcA, hArcB, _, _⟩
    have hAr : rA D ≤ 1 := by
      calc
        rA D ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖D‖])
        _ = 1 := by norm_num
    have hBr : rB D ≤ 1 := by
      calc
        rB D ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖D-e‖])
        _ = 1 := by norm_num
    have hr : 0 ≤ rA D * rB D := mul_nonneg hrA.le hrB.le
    have hr1 : rA D * rB D ≤ 1 := by nlinarith
    have hpull : ∀ t ∈ Set.uIoc (0 : ℝ) C.TA, ∀ s ∈ Set.uIoc (0 : ℝ) C.TB,
        ‖rA D * rB D * bKernel f D (u D C t) (v D C s)‖ ≤ 4 := by
      intro t ht s hs
      have ht' : t ∈ Set.Icc (0 : ℝ) C.TA := by
        rw [Set.uIoc_of_le hTA.le] at ht
        exact ⟨ht.1.le, ht.2⟩
      have hs' : s ∈ Set.Icc (0 : ℝ) C.TB := by
        rw [Set.uIoc_of_le hTB.le] at hs
        exact ⟨hs.1.le, hs.2⟩
      have hp : u D C t ∈ arcA D := by rw [hArcA]; exact Set.mem_image_of_mem _ ht'
      have hq : v D C s ∈ arcB D := by rw [hArcB]; exact Set.mem_image_of_mem _ hs'
      have hk := bKernel_uniform_bound f D (u D C t) (v D C s) hD hp hq
      rw [norm_mul, Real.norm_of_nonneg hr]
      exact (mul_le_mul_of_nonneg_left hk hr).trans (by nlinarith)
    have hin : ∀ t ∈ Set.uIoc (0 : ℝ) C.TA,
        ‖∫ s in (0 : ℝ)..C.TB, rA D * rB D * bKernel f D (u D C t) (v D C s)‖ ≤ 4 * C.TB := by
      intro t ht
      simpa only [sub_zero, abs_of_pos hTB] using
        intervalIntegral.norm_integral_le_of_norm_le_const (hpull t ht)
    have hout := intervalIntegral.norm_integral_le_of_norm_le_const hin
    simp only [sub_zero, abs_of_pos hTA] at hout
    apply hout.trans
    have hmul : C.TB * C.TA ≤ (2 * Real.pi) * (2 * Real.pi) :=
      mul_le_mul hTBpi hTApi hTA.le (by positivity)
    nlinarith
  · rw [(inactive_cross_zero f D hD hact).2]
    simp only [norm_zero]
    positivity
