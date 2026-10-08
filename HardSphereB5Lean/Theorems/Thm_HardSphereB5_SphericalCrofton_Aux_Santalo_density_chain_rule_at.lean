import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_density_chain_rule_at
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.density_chain_rule_at :
    ∀ (f : Kern) (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1) (hC : IsChart D C) (t s : ℝ) (ht : t ∈ Set.Icc 0 C.TA) (hs : s ∈ Set.Icc 0 C.TB) (hx : inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1), J f D C t s = -Q12 f D C t s + H f D C t s :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_density_chain_rule_at
