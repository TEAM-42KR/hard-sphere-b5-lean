import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_rectangle_product_integrability
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_rectangle_slice_FTC_data
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_rectangle_regular_canonical (f : Kern) (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D-e‖ < 1) (hC : IsChart D C)
    (h00 : delta D C 0 0 = 0) (hdd : delta D C C.TA C.TB = 0)
    (hrange : ∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB,
      ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) →
      inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1) : Integrable (Function.uncurry (Q12 f D C)) ((volume.restrict (Set.Ioc 0 C.TA)).prod (volume.restrict (Set.Ioc 0 C.TB))) ∧ Integrable (Function.uncurry (H f D C)) ((volume.restrict (Set.Ioc 0 C.TA)).prod (volume.restrict (Set.Ioc 0 C.TB))) ∧ (∀ s ∈ Set.Ioo 0 C.TB, ContinuousOn (fun t => Q2 f D C t s) (Set.Icc 0 C.TA)) ∧ (∀ s ∈ Set.Ioo 0 C.TB, ∀ t ∈ Set.Ioo 0 C.TA, HasDerivAt (fun z => Q2 f D C z s) (Q12 f D C t s) t) ∧ (∀ s ∈ Set.Ioo 0 C.TB, IntervalIntegrable (fun t => Q12 f D C t s) volume 0 C.TA) ∧ (∀ t ∈ ({0, C.TA} : Set ℝ), ContinuousOn (Q f D C t) (Set.Icc 0 C.TB)) ∧ (∀ t ∈ ({0, C.TA} : Set ℝ), ∀ s ∈ Set.Ioo 0 C.TB, HasDerivAt (Q f D C t) (Q2 f D C t s) s) ∧ (∀ t ∈ ({0, C.TA} : Set ℝ), IntervalIntegrable (Q2 f D C t) volume 0 C.TB) := by
  obtain ⟨hQ,hH⟩ := rectangle_product_integrability f D C hD hoff hR hC h00 hdd hrange
  exact ⟨hQ,hH,rectangle_slice_FTC_data f D C hD hoff hR hC hrange⟩
