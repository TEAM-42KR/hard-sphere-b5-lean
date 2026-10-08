import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_half_label_partition (μA μB : Measure Pt) [SFinite μA] [SFinite μB] (H : Pt → Pt → ℝ) (hH : Integrable (Function.uncurry H) ((μA + μB).prod (μA + μB))) (hSym : ∀ u v, H u v = H v u) : (1 / 2 : ℝ) * (∫ u, ∫ v, H u v ∂(μA + μB) ∂(μA + μB)) = (1 / 2 : ℝ) * (∫ u, ∫ v, H u v ∂μA ∂μA) + (1 / 2 : ℝ) * (∫ u, ∫ v, H u v ∂μB ∂μB) + (∫ u, ∫ v, H u v ∂μB ∂μA) := by
  change Integrable (fun q : Pt × Pt => H q.1 q.2) ((μA + μB).prod (μA + μB)) at hH
  have h0 := hH
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add] at h0
  have hAA := h0.left_of_add_measure.left_of_add_measure
  have hAB := h0.left_of_add_measure.right_of_add_measure
  have hBA := h0.right_of_add_measure.left_of_add_measure
  have hBB := h0.right_of_add_measure.right_of_add_measure
  have hswap : (∫ u, ∫ v, H u v ∂μA ∂μB) = ∫ u, ∫ v, H u v ∂μB ∂μA := by
    rw [integral_integral_swap hBA]
    apply integral_congr_ae
    filter_upwards with u
    apply integral_congr_ae
    filter_upwards with v
    exact hSym v u
  have hprod : (∫ u, ∫ v, H u v ∂(μA + μB) ∂(μA + μB)) = ∫ q, H q.1 q.2 ∂((μA + μB).prod (μA + μB)) := integral_integral hH
  rw [hprod]
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  rw [integral_add_measure h0.left_of_add_measure h0.right_of_add_measure,
      integral_add_measure hAA hAB, integral_add_measure hBA hBB]
  rw [integral_prod _ hAA, integral_prod _ hAB, integral_prod _ hBA, integral_prod _ hBB, hswap]
  ring

