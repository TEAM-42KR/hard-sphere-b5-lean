import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_lintegral_count_eq_three_radial_fibers
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.lintegral_count_eq_three_radial_fibers :
    ∀ (γ a b : ℝ → E3) (S : Set ℝ)
    (hs : ∀ s ∈ S, ‖γ s‖ = 1) (hinj : Set.InjOn γ S)
    (hframe : ∀ s ∈ S, Orthonormal ℝ ![a s, b s, γ s] ∧ cross (a s) (b s) = γ s)
    (hN : Measurable (fun p : E3 => ((greatCircle p ∩ γ '' S).encard : ENNReal))),
    let Ψ : E3 → E3 := fun y => y 2 • (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0))
    let D : Set E3 := {y | y 0 ∈ S ∧ y 1 ∈ Set.Ioc 0 (2 * Real.pi) ∧ y 2 ∈ Set.Ioo 0 1}
    (∫⁻ p, ((greatCircle p ∩ γ '' S).encard : ENNReal) ∂dOmega) =
      3 * ∫⁻ x, ((D ∩ Ψ ⁻¹' {x}).encard : ENNReal) :=
  @proof_SphereGeom_Aux_Crofton_lintegral_count_eq_three_radial_fibers
