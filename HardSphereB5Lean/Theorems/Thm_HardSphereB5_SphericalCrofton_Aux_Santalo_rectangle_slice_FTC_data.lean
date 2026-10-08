import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_rectangle_slice_FTC_data
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.rectangle_slice_FTC_data :
    ∀ (f : Kern) (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1) (hC : IsChart D C) (hRange : ∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB, ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) → inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1), (∀ s ∈ Set.Ioo 0 C.TB, ContinuousOn (fun t => Q2 f D C t s) (Set.Icc 0 C.TA)) ∧
    (∀ s ∈ Set.Ioo 0 C.TB, ∀ t ∈ Set.Ioo 0 C.TA, HasDerivAt (fun z => Q2 f D C z s) (Q12 f D C t s) t) ∧
    (∀ s ∈ Set.Ioo 0 C.TB, IntervalIntegrable (fun t => Q12 f D C t s) volume 0 C.TA) ∧
    (∀ t ∈ ({0,C.TA} : Set ℝ), ContinuousOn (Q f D C t) (Set.Icc 0 C.TB)) ∧
    (∀ t ∈ ({0,C.TA} : Set ℝ), ∀ s ∈ Set.Ioo 0 C.TB, HasDerivAt (Q f D C t) (Q2 f D C t s) s) ∧
    (∀ t ∈ ({0,C.TA} : Set ℝ), IntervalIntegrable (Q2 f D C t) volume 0 C.TB) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_rectangle_slice_FTC_data
