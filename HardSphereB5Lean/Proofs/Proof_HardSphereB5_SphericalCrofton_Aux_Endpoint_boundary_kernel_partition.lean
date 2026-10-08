import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_restrict_union_null
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_half_label_partition
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_density_swap
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundary_kernel_partition (f : Kern) (D : Pt)
    (hA : MeasurableSet (arcA D)) (hB : MeasurableSet (arcB D))
    (hAB : arcMeasure (arcA D ∩ arcB D) = 0)
    (hAf : arcMeasure (arcA D) < ⊤) (hBf : arcMeasure (arcB D) < ⊤)
    (hInt : Integrable (pairKernel f D) (pairMu D)) :
    (1 / 2 : ℝ) * (∫ q, pairKernel f D q ∂pairMu D) =
      AAf f D + BBf f D + ABf f D := by
  classical
  let μA := arcMeasure.restrict (arcA D)
  let μB := arcMeasure.restrict (arcB D)
  letI : IsFiniteMeasure μA := ⟨by simpa [μA] using hAf⟩
  letI : IsFiniteMeasure μB := ⟨by simpa [μB] using hBf⟩
  have hμ : boundaryMu D = μA + μB :=
    restrict_union_null arcMeasure (arcA D) (arcB D) hB hAB
  let H : Pt → Pt → ℝ := fun u v => pairKernel f D (u, v)
  have hH : Integrable (Function.uncurry H) ((μA + μB).prod (μA + μB)) := by
    have hI := hInt
    unfold pairMu at hI
    rw [hμ] at hI
    exact hI
  have hSym : ∀ u v, H u v = H v u := by
    intro u v
    dsimp [H, pairKernel, pairDelta, pairDens]
    rw [real_inner_comm u v, density_swap]
  have hTauA : ∀ᵐ u ∂μA, boundaryTau D u = tanA D u := by
    filter_upwards [ae_restrict_mem (μ := arcMeasure) hA] with u hu
    simp only [boundaryTau, if_pos hu]
  have hzero : μB (arcA D) = 0 := by
    dsimp [μB]
    rw [Measure.restrict_apply hA]
    exact hAB
  have hNotA : ∀ᵐ u ∂μB, u ∉ arcA D := by
    apply ae_iff.mpr
    simpa only [not_not, Set.setOf_mem_eq] using hzero
  have hTauB : ∀ᵐ u ∂μB, boundaryTau D u = tanB D u := by
    filter_upwards [hNotA] with u hu
    simp only [boundaryTau, if_neg hu]
  have hAA : (1 / 2 : ℝ) * (∫ u, ∫ v, H u v ∂μA ∂μA) = AAf f D := by
    unfold AAf
    apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    apply integral_congr_ae
    filter_upwards [hTauA] with u hu
    apply integral_congr_ae
    filter_upwards [hTauA] with v hv
    simp only [H, pairKernel, pairDelta, pairDens, hu, hv]
  have hBB : (1 / 2 : ℝ) * (∫ u, ∫ v, H u v ∂μB ∂μB) = BBf f D := by
    unfold BBf
    apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    apply integral_congr_ae
    filter_upwards [hTauB] with u hu
    apply integral_congr_ae
    filter_upwards [hTauB] with v hv
    simp only [H, pairKernel, pairDelta, pairDens, hu, hv]
  have hCross : (∫ u, ∫ v, H u v ∂μB ∂μA) = ABf f D := by
    unfold ABf
    apply integral_congr_ae
    filter_upwards [hTauA] with u hu
    apply integral_congr_ae
    filter_upwards [hTauB] with v hv
    simp only [H, pairKernel, pairDelta, pairDens, hu, hv]
  have hprod : (∫ q, pairKernel f D q ∂pairMu D) =
      ∫ u, ∫ v, H u v ∂(μA + μB) ∂(μA + μB) := by
    change (∫ q, Function.uncurry H q ∂(boundaryMu D).prod (boundaryMu D)) = _
    rw [hμ]
    exact integral_prod _ hH
  rw [hprod]
  simpa only [hAA, hBB, hCross] using half_label_partition μA μB H hH hSym
