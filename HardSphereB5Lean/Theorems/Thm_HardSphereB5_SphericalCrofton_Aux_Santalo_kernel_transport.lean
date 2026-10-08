import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_kernel_transport
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.kernel_transport :
    ∀ (D : Pt) (C : Charts) (hC : IsChart D C) (g : Pt → Pt → ℝ) (hg : Measurable (Function.uncurry g)), (∫ p in arcA D, ∫ q in arcB D, g p q ∂arcMeasure ∂arcMeasure) = ∫ t in (0 : ℝ)..C.TA, ∫ s in (0 : ℝ)..C.TB, rA D * rB D * g (u D C t) (v D C s) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_kernel_transport
