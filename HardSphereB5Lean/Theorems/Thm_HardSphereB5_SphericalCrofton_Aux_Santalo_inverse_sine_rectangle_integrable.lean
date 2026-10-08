import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_inverse_sine_rectangle_integrable
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo Filter
open HardSphereB5.Lean (Pt e)
open scoped Topology

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.inverse_sine_rectangle_integrable :
    ∀ (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D-e‖ < 1) (hC : IsChart D C)
    (h00 : delta D C 0 0 = 0) (hdd : delta D C C.TA C.TB = 0)
    (hrange : ∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB,
      ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) →
      inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1), IntegrableOn (fun z : ℝ × ℝ => (Real.sin (delta D C z.1 z.2))⁻¹)
      (Set.Icc 0 C.TA ×ˢ Set.Icc 0 C.TB) volume :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_inverse_sine_rectangle_integrable
