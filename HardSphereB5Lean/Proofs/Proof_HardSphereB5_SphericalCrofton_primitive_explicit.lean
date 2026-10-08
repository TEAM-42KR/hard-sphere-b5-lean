import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_primitive_explicit (d : ℝ) :
    Pprim .one d = d ^ 2 / 2 + 2 * Real.cos d - 2 + (√3 - π / 3) * d ∧
      Pprim .cos d = (π / 12 + √3 / 8) * d - d ^ 2 / 8 + Real.cos (2 * d) / 8 - 1 / 8 := by
  let F1 : ℝ → ℝ := fun x => x ^ 2 / 2 + 2 * Real.cos x - 2 + (√3 - π / 3) * x
  let Fc : ℝ → ℝ := fun x => (π / 12 + √3 / 8) * x - x ^ 2 / 8 + Real.cos (2 * x) / 8 - 1 / 8
  have hd1 : ∀ x, HasDerivAt F1 (phiK .one x) x := by
    intro x
    convert (((((hasDerivAt_id x).pow 2).div_const 2).add ((Real.hasDerivAt_cos x).const_mul 2)).sub_const 2).add ((hasDerivAt_id x).const_mul (√3 - π / 3)) using 1 <;> first | rfl | (simp only [phiK, id_eq]; ring)
  have hdc : ∀ x, HasDerivAt Fc (phiK .cos x) x := by
    intro x
    convert ((((hasDerivAt_id x).const_mul (π / 12 + √3 / 8)).sub (((hasDerivAt_id x).pow 2).div_const 8)).add ((((hasDerivAt_id x).const_mul 2).cos).div_const 8)).sub_const (1 / 8) using 1 <;> first | rfl | (simp only [phiK, id_eq]; ring)
  have hc1 : Continuous (phiK .one) := by unfold phiK; fun_prop
  have hcc : Continuous (phiK .cos) := by unfold phiK; fun_prop
  constructor
  · have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x (_ : x ∈ Set.uIcc 0 d) => hd1 x) (hc1.intervalIntegrable 0 d)
    simpa [Pprim, F1] using hh
  · have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x (_ : x ∈ Set.uIcc 0 d) => hdc x) (hcc.intervalIntegrable 0 d)
    simpa [Pprim, Fc] using hh

