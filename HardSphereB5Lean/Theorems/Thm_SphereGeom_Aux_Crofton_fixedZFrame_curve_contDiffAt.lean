import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_fixedZFrame_curve_contDiffAt
import HardSphereB5Lean.Definitions.Def_SphereGeom_fixedZFrame
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.fixedZFrame_curve_contDiffAt :
    ∀ (γ : ℝ → E3) (hγ : ContDiff ℝ 1 γ) (t : ℝ) (hQ : (γ t) 0 ^ 2 + (γ t) 1 ^ 2 ≠ 0), ContDiffAt ℝ 1 (fun s => fixedZA (γ s)) t ∧ ContDiffAt ℝ 1 (fun s => fixedZB (γ s)) t :=
  @proof_SphereGeom_Aux_Crofton_fixedZFrame_curve_contDiffAt
