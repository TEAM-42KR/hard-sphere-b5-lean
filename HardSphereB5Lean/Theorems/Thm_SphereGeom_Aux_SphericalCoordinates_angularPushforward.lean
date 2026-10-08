import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_SphericalCoordinates_angularPushforward
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.SphericalCoordinates.angularPushforward :
    let coord : ℝ × ℝ → E3 := fun p =>
      (Real.sin p.1 * Real.cos p.2) • (EuclideanSpace.basisFun (Fin 3) ℝ) 0 +
      (Real.sin p.1 * Real.sin p.2) • (EuclideanSpace.basisFun (Fin 3) ℝ) 1 +
      Real.cos p.1 • (EuclideanSpace.basisFun (Fin 3) ℝ) 2
    (((volume : Measure ℝ).restrict (Set.Ioc 0 Real.pi)).prod
      ((volume : Measure ℝ).restrict (Set.Ioc 0 (2 * Real.pi)))).withDensity
      (fun p => ENNReal.ofReal (Real.sin p.1)) |>.map coord = dOmega :=
  @proof_SphereGeom_Aux_SphericalCoordinates_angularPushforward
