import HardSphereB5Lean.Proofs.Proof_SphereGeom_two_cap_normal_moment
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SphereGeom.two_cap_normal_moment :
    ∀ (e : Fin 3 → E3) (he : Orthonormal ℝ e) (A K L h b : ℝ), inner ℝ (e 2) (∫ u in cap (A • e 0) h ∩ cap (K • e 0 + L • e 1) b, u ∂dOmega) = 0 :=
  @proof_SphereGeom_two_cap_normal_moment
