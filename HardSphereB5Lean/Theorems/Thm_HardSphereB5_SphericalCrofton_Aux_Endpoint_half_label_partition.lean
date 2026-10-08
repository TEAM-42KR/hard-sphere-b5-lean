import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_half_label_partition
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.half_label_partition :
    ∀ (μA μB : Measure Pt) [SFinite μA] [SFinite μB] (H : Pt → Pt → ℝ) (hH : Integrable (Function.uncurry H) ((μA + μB).prod (μA + μB))) (hSym : ∀ u v, H u v = H v u), (1 / 2 : ℝ) * (∫ u, ∫ v, H u v ∂(μA + μB) ∂(μA + μB)) = (1 / 2 : ℝ) * (∫ u, ∫ v, H u v ∂μA ∂μA) + (1 / 2 : ℝ) * (∫ u, ∫ v, H u v ∂μB ∂μB) + (∫ u, ∫ v, H u v ∂μB ∂μA) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_half_label_partition
