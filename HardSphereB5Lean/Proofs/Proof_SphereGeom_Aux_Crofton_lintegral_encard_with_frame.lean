import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_lintegral_count_eq_three_radial_fibers
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_lintegral_encard_preimage_eq_jacobian
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_hasFDerivAt_radial_incidence
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_fderiv_det_radial_incidence
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_parameter_frame_lintegral
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_deriv_orthogonal_of_eventually
set_option autoImplicit false
open MeasureTheory SphereGeom

set_option backward.isDefEq.respectTransparency false in
theorem proof_SphereGeom_Aux_Crofton_lintegral_encard_with_frame (γ a b : ℝ → E3) (S : Set ℝ) (hS : MeasurableSet S)
    (hma : Measurable a) (hmb : Measurable b) (hmγ : Measurable γ)
    (hs : ∀ s ∈ S, ‖γ s‖ = 1) (hinj : Set.InjOn γ S)
    (hframe : ∀ s ∈ S, Orthonormal ℝ ![a s, b s, γ s] ∧ cross (a s) (b s) = γ s)
    (hda : ∀ s ∈ S, DifferentiableAt ℝ a s)
    (hdb : ∀ s ∈ S, DifferentiableAt ℝ b s)
    (hdγ : ∀ s ∈ S, DifferentiableAt ℝ γ s)
    (hoa : ∀ s ∈ S, (fun t => inner ℝ (a t) (γ t)) =ᶠ[nhds s] (fun _ => 0))
    (hob : ∀ s ∈ S, (fun t => inner ℝ (b t) (γ t)) =ᶠ[nhds s] (fun _ => 0))
    (htan : ∀ s ∈ S, inner ℝ (deriv γ s) (γ s) = 0)
    (hN : Measurable (fun p : E3 => ((greatCircle p ∩ γ '' S).encard : ENNReal))) :
    ∫⁻ p, ((greatCircle p ∩ γ '' S).encard : ENNReal) ∂dOmega =
      4 * ∫⁻ s in S, ENNReal.ofReal ‖deriv γ s‖ := by
  let Ψ : E3 → E3 := fun y => y 2 • (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0))
  let D : Set E3 := {y | y 0 ∈ S ∧ y 1 ∈ Set.Ioc 0 (2 * Real.pi) ∧ y 2 ∈ Set.Ioo 0 1}
  have hp (i : Fin 3) : Measurable (fun x : E3 => x i) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) i).measurable
  have hD : MeasurableSet D :=
    (hp 0 hS).inter ((hp 1 measurableSet_Ioc).inter (hp 2 measurableSet_Ioo))
  have hd : ∀ x ∈ D, HasFDerivWithinAt Ψ (fderiv ℝ Ψ x) D x := by
    intro x hx
    have h := SphereGeom.Aux.Crofton.hasFDerivAt_radial_incidence a b
      (deriv a (x 0)) (deriv b (x 0)) x (hda _ hx.1).hasDerivAt (hdb _ hx.1).hasDerivAt
    exact (h.congr_fderiv h.fderiv.symm).hasFDerivWithinAt
  have hdet : ∀ x ∈ D, ENNReal.ofReal |(fderiv ℝ Ψ x).det| =
      ENNReal.ofReal ((x 2) ^ 2 * |inner ℝ (Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)) (deriv γ (x 0))|) := by
    intro x hx
    have h := SphereGeom.Aux.Crofton.fderiv_det_radial_incidence a b
      (deriv a (x 0)) (deriv b (x 0)) (γ (x 0)) (deriv γ (x 0)) x
      (hda _ hx.1).hasDerivAt (hdb _ hx.1).hasDerivAt (hframe _ hx.1).2
      (SphereGeom.Aux.Crofton.deriv_orthogonal_of_eventually a γ (x 0) (hda _ hx.1) (hdγ _ hx.1) (hoa _ hx.1))
      (SphereGeom.Aux.Crofton.deriv_orthogonal_of_eventually b γ (x 0) (hdb _ hx.1) (hdγ _ hx.1) (hob _ hx.1))
    dsimp only [Ψ]
    simpa only [abs_mul, abs_sq] using congrArg (fun z : ℝ => ENNReal.ofReal |z|) h
  have hfiber : (fun x => ((D ∩ Ψ ⁻¹' {x}).encard : ENNReal)) =
      (fun x => ({y : E3 | y ∈ D ∧ Ψ y = x}.encard : ENNReal)) := by
    rfl
  calc
    (∫⁻ p, ((greatCircle p ∩ γ '' S).encard : ENNReal) ∂dOmega) =
        3 * ∫⁻ x, ((D ∩ Ψ ⁻¹' {x}).encard : ENNReal) :=
      SphereGeom.Aux.Crofton.lintegral_count_eq_three_radial_fibers γ a b S hs hinj hframe hN
    _ = 3 * ∫⁻ x in D, ENNReal.ofReal |(fderiv ℝ Ψ x).det| := by
      rw [hfiber, SphereGeom.Aux.Crofton.lintegral_encard_preimage_eq_jacobian
        volume Ψ (fderiv ℝ Ψ) D hD (measurable_fderiv ℝ Ψ) hd]
    _ = 3 * ∫⁻ x in D, ENNReal.ofReal ((x 2) ^ 2 * |inner ℝ
        (Real.cos (x 1) • a (x 0) + Real.sin (x 1) • b (x 0)) (deriv γ (x 0))|) := by
      congr 1
      exact setLIntegral_congr_fun hD hdet
    _ = 3 * ((4 / 3 : ENNReal) * ∫⁻ s in S, ENNReal.ofReal ‖deriv γ s‖) := by
      congr 1
      exact SphereGeom.Aux.Crofton.parameter_frame_lintegral S hS a b γ (deriv γ)
        hma hmb hmγ (measurable_deriv γ) (fun s hs => (hframe s hs).1) htan
    _ = 4 * ∫⁻ s in S, ENNReal.ofReal ‖deriv γ s‖ := by
      rw [← mul_assoc]
      have hrat : (3 : ENNReal) * (4 / 3) = 4 := by
        rw [div_eq_mul_inv, mul_left_comm,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
      rw [hrat]
