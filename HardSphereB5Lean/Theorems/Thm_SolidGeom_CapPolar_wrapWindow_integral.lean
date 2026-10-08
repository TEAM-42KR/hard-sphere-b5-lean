import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_wrapWindow_integral
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_wrapWindow
set_option autoImplicit false
noncomputable section
open MeasureTheory

theorem SolidGeom.CapPolar.wrapWindow_integral :
    ∀ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : Continuous f)
    (T A B : ℝ) (hT : 0<T) (hA : 0≤A) (hAT : A<T) (hAB : A<B) (hBT : B<A+T)
    (hp : Function.Periodic f T), (∫ x in SolidGeom.CapPolar.wrapWindow T A B, f x)=∫ x in A..B, f x :=
  @proof_SolidGeom_CapPolar_wrapWindow_integral
