import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_SphericalCoordinates_cosHeightMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.Aux.SphericalCoordinates.cosHeightMeasure :
    ((volume.restrict (Set.Ioc (0 : ℝ) Real.pi)).withDensity
      (fun θ => ENNReal.ofReal (Real.sin θ))).map Real.cos =
    volume.restrict (Set.Icc (-1 : ℝ) 1) :=
  @proof_SphereGeom_Aux_SphericalCoordinates_cosHeightMeasure
