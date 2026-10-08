import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_actual_radial_jacobian
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
open SphereGeom HardSphereB5.SphericalCrofton
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.actual_radial_jacobian :
    ∀ (γ1 γ2 : ℝ → E3) (τ1 τ2 : E3) (x : E3)
    (hγ1 : HasDerivAt γ1 τ1 (x 0)) (hγ2 : HasDerivAt γ2 τ2 (x 1))
    (hu : ‖γ1 (x 0)‖ = 1) (hv : ‖γ2 (x 1)‖ = 1)
    (hcross : cross (γ1 (x 0)) (γ2 (x 1)) ≠ 0),
    let Φ : E3 → E3 := fun y => y 2 • unitDir (cross (γ1 (y 0)) (γ2 (y 1)))
    let p : E3 := unitDir (cross (γ1 (x 0)) (γ2 (x 1)))
    HasFDerivAt Φ (fderiv ℝ Φ x) x ∧
      |LinearMap.det (fderiv ℝ Φ x).toLinearMap| =
        (x 2) ^ 2 * |inner ℝ p τ1| * |inner ℝ p τ2| /
          Real.sin (Real.arccos (inner ℝ (γ1 (x 0)) (γ2 (x 1)))) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_actual_radial_jacobian
