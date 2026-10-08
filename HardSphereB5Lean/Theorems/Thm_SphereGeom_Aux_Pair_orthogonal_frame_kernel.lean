import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_orthogonal_frame_kernel
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.orthogonal_frame_kernel :
    ∀ (a b p : E3) (hab : Orthonormal ℝ ![a,b,p]), (∀ s t : ℝ, Real.sqrt (1-(inner ℝ (Real.cos s • a + Real.sin s • b)
      (Real.cos t • a + Real.sin t • b))^2) = |Real.sin (s-t)|) ∧
    (∀ (u c d : E3) (hcd : Orthonormal ℝ ![c,d,u]) (t : ℝ)
      (hp : p = Real.cos t • c + Real.sin t • d) (f : E3 → ENNReal) (hf : Measurable f),
      (∫⁻ v in Set.Ioc 0 (2*Real.pi),
        f (Real.cos v • a + Real.sin v • b) * ENNReal.ofReal (Real.sqrt
          (1-(inner ℝ u (Real.cos v • a + Real.sin v • b))^2))) =
      ∫⁻ v in Set.Ioc 0 (2*Real.pi),
        f (Real.cos v • u + Real.sin v • (-Real.sin t • c + Real.cos t • d)) *
          ENNReal.ofReal |Real.sin v|) :=
  @proof_SphereGeom_Aux_Pair_orthogonal_frame_kernel
