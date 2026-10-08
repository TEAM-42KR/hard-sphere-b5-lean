import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_SphericalCoordinates_standardIntegral
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.SphericalCoordinates.standardIntegral :
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E3 → F) (hf : Integrable f dOmega), ∫ u, f u ∂dOmega =
      ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Real.sin θ • f ((Real.sin θ * Real.cos φ) • (EuclideanSpace.basisFun (Fin 3) ℝ) 0 +
          (Real.sin θ * Real.sin φ) • (EuclideanSpace.basisFun (Fin 3) ℝ) 1 +
          Real.cos θ • (EuclideanSpace.basisFun (Fin 3) ℝ) 2) :=
  @proof_SphereGeom_Aux_SphericalCoordinates_standardIntegral
