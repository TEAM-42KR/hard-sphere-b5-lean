import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom
theorem proof_SphereGeom_Aux_Pair_periodic_lintegral_translate (f : ℝ → ENNReal) (T : ℝ) (hT : 0 < T)
    (hf : Function.Periodic f T) (a s : ℝ) :
    (∫⁻ t in Set.Ioc a (a + T), f (t + s)) = ∫⁻ t in Set.Ioc a (a + T), f t := by
  letI : Fact (0 < T) := ⟨hT⟩
  calc
    (∫⁻ t in Set.Ioc a (a + T), f (t + s)) =
        ∫⁻ x : AddCircle T, hf.lift (x + (s : AddCircle T)) := by
      simpa only [← AddCircle.coe_add, Function.Periodic.lift_coe] using
        (AddCircle.lintegral_preimage T a (fun x => hf.lift (x + (s : AddCircle T))))
    _ = ∫⁻ x : AddCircle T, hf.lift x := lintegral_add_right_eq_self _ _
    _ = ∫⁻ t in Set.Ioc a (a + T), f t := by
      simpa only [Function.Periodic.lift_coe] using (AddCircle.lintegral_preimage T a hf.lift).symm
