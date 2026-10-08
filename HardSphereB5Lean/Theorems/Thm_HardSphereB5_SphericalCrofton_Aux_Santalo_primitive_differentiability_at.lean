import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_primitive_differentiability_at
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.primitive_differentiability_at :
    ∀ (f : Kern) (D : Pt) (C : Charts) (t s : ℝ)
    (hx : inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1), HasDerivAt (Q f D C t) (Q2 f D C t s) s ∧
    HasDerivAt (fun z => Q2 f D C z s) (Q12 f D C t s) t :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_primitive_differentiability_at
