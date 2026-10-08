import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_primitive_chain
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.mixed_primitive_chain :
    ∀ (f : Kern) (D : Pt) (C : Charts) (t s : ℝ) (hx : inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1), Q12 f D C t s =
      (if delta D C t s < π / 3 then deriv (phiK f) (delta D C t s) else 0) *
        deriv (fun z => delta D C z s) t * deriv (delta D C t) s +
      cutKern f (delta D C t s) * deriv (fun z => deriv (delta D C z) s) t :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_primitive_chain
