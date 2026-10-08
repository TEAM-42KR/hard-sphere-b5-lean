import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_wrapWindow_integral_any
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_wrapWindow_integral
set_option autoImplicit false
noncomputable section
open MeasureTheory

theorem SolidGeom.CapPolar.wrapWindow_integral_any :
    ∀ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : Continuous f)
    (T A B : ℝ) (hT : 0<T) (hAB : A<B) (hBT : B<A+T) (hp : Function.Periodic f T), (∫ x in SolidGeom.CapPolar.wrapWindow T A B, f x)=∫ x in A..B, f x :=
  @proof_SolidGeom_CapPolar_wrapWindow_integral_any
