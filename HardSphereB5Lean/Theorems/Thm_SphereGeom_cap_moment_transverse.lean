import HardSphereB5Lean.Proofs.Proof_SphereGeom_cap_moment_transverse
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SphereGeom.cap_moment_transverse :
    ∀ (e : Fin 3 → E3) (he : Orthonormal ℝ e) (h k l b : ℝ) (hh0 : -1 ≤ h) (hh1 : h ≤ 1) (hl : 0 < l), inner ℝ (e 0) (∫ u in cap (e 2) h ∩ cap (k • e 2 + l • e 0) b, u ∂dOmega) = (2 / l) * (∫ t in h..1, Real.sqrt (l ^ 2 * (1 - t ^ 2) - (b - k * t) ^ 2)) :=
  @proof_SphereGeom_cap_moment_transverse
