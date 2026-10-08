import HardSphereB5Lean.Proofs.Proof_SphereGeom_integral_dOmega_frame
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.integral_dOmega_frame :
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) (f : E3 → F) (hf : Integrable f dOmega), ∫ u, f u ∂dOmega =
      ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Real.sin θ • f ((Real.sin θ * Real.cos φ) • e 0 + (Real.sin θ * Real.sin φ) • e 1 +
          Real.cos θ • e 2) :=
  @proof_SphereGeom_integral_dOmega_frame
