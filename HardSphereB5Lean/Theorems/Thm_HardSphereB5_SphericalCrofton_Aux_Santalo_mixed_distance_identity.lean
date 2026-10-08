import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_distance_identity
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Santalo.mixed_distance_identity :
    ∀ (D : Pt) (C : Charts) (hC : IsChart D C)
    (t s : ℝ) (ht : t ∈ Set.Icc 0 C.TA) (hs : s ∈ Set.Icc 0 C.TB)
    (hx : inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1), -deriv (fun z => deriv (delta D C z) s) t =
      (inner ℝ (nAv D) (v D C s) - inner ℝ (nAv D) (u D C t) * inner ℝ (u D C t) (v D C s)) *
      (inner ℝ (nBv D) (u D C t) - inner ℝ (nBv D) (v D C s) * inner ℝ (u D C t) (v D C s)) /
      (Real.sin (Real.arccos (inner ℝ (u D C t) (v D C s))) ^ 3) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_distance_identity
