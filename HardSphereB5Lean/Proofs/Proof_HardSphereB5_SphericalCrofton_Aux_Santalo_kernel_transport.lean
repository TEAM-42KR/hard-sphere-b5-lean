import Mathlib
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_restrict_circle
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_kernel_transport (D : Pt) (C : Charts) (hC : IsChart D C) (g : Pt → Pt → ℝ) (hg : Measurable (Function.uncurry g)) : (∫ p in arcA D, ∫ q in arcB D, g p q ∂arcMeasure ∂arcMeasure) = ∫ t in (0 : ℝ)..C.TA, ∫ s in (0 : ℝ)..C.TB, rA D * rB D * g (u D C t) (v D C s) := by
  rcases hC with ⟨hEA, hEB, hrA, hrB, hTA, hTB, hTApi, hTBpi, hArcA, hArcB, _, _⟩
  have hu : Continuous (u D C) := by unfold u circlePt; fun_prop
  have hv : Continuous (v D C) := by unfold v circlePt; fun_prop
  have hμA : arcMeasure.restrict (arcA D) =
      ENNReal.ofReal (rA D) • (volume.restrict (Set.Icc 0 C.TA)).map (u D C) := by
    rw [hArcA]
    exact SphereGeom.arcMeasure_restrict_circle C.oA C.EA hEA (rA D) hrA
      0 C.TA hTA.le (by simpa using hTApi)
  have hμB : arcMeasure.restrict (arcB D) =
      ENNReal.ofReal (rB D) • (volume.restrict (Set.Icc 0 C.TB)).map (v D C) := by
    rw [hArcB]
    exact SphereGeom.arcMeasure_restrict_circle C.oB C.EB hEB (rB D) hrB
      0 C.TB hTB.le (by simpa using hTBpi)
  have hsec (p : Pt) : Measurable (g p) := hg.comp (measurable_const.prodMk measurable_id)
  have hinner (p : Pt) : (∫ q in arcB D, g p q ∂arcMeasure) =
      rB D * ∫ s in Set.Icc 0 C.TB, g p (v D C s) := by
    rw [hμB, integral_smul_measure, integral_map hv.aemeasurable (hsec p).aestronglyMeasurable]
    simp [ENNReal.toReal_ofReal hrB.le]
  simp_rw [hinner]
  rw [hμA, integral_smul_measure]
  have hmeas : StronglyMeasurable (fun p : Pt =>
      rB D * ∫ s in Set.Icc 0 C.TB, g p (v D C s)) := by
    apply StronglyMeasurable.const_mul
    apply StronglyMeasurable.integral_prod_right
    exact (hg.comp (measurable_fst.prodMk (hv.measurable.comp measurable_snd))).stronglyMeasurable
  rw [integral_map hu.aemeasurable hmeas.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hrA.le, smul_eq_mul]
  simp_rw [integral_const_mul, integral_Icc_eq_integral_Ioc]
  simp_rw [intervalIntegral.integral_of_le hTA.le, intervalIntegral.integral_of_le hTB.le,
    integral_const_mul]
  ring
