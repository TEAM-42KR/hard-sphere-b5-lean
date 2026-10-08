import HardSphereB5Lean.Proofs.Proof_SphereGeom_twoCap_area_frame
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.twoCap_area_frame :
    ∀ (e : Fin 3 → E3) (he : Orthonormal ℝ e)
 (v w : E3) (h k : ℝ)
 (hf : Integrable ((cap v h ∩ cap w k).indicator (fun _ : E3 => (1 : ℝ))) dOmega), (dOmega (cap v h ∩ cap w k)).toReal =
 ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
 Real.sin θ * (cap v h ∩ cap w k).indicator (fun _ : E3 => (1 : ℝ))
 ((Real.sin θ * Real.cos φ) • e 0 + (Real.sin θ * Real.sin φ) • e 1 + Real.cos θ • e 2) :=
  @proof_SphereGeom_twoCap_area_frame
