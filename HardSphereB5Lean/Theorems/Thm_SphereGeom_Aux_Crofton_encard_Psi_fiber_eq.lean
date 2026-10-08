import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_encard_Psi_fiber_eq
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_angle_unique_Ioc
import Mathlib.Data.Set.Card
set_option autoImplicit false

theorem SphereGeom.Aux.Crofton.encard_Psi_fiber_eq :
    ∀ (a b g : ℝ → SphereGeom.E3) (S : Set ℝ) (hframe : ∀ s ∈ S, Orthonormal ℝ ![a s, b s, g s] ∧ SphereGeom.cross (a s) (b s) = g s) (x : SphereGeom.E3) (hx : x ≠ 0) (hxn : ‖x‖ < 1),
    let Ψ : SphereGeom.E3 → SphereGeom.E3 := fun y => y 2 • (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0)); let D : Set SphereGeom.E3 := {y | y 0 ∈ S ∧ y 1 ∈ Set.Ioc 0 (2 * Real.pi) ∧ y 2 ∈ Set.Ioo 0 1}; (D ∩ Ψ ⁻¹' {x}).encard = {s : ℝ | s ∈ S ∧ inner ℝ x (g s) = 0}.encard :=
  @proof_SphereGeom_Aux_Crofton_encard_Psi_fiber_eq
