import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_HitMass_regular_cone_geometry
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.HitMass.regular_cone_geometry :
    ∀ (K : Set Pt) (hK : IsRegularRegionCrofton K),
    let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}; IsClosed C ∧ Convex ℝ C ∧ (∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C) ∧ (interior C).Nonempty ∧ (∀ u : Pt, ‖u‖ = 1 → (u ∈ frontier C ↔ u ∈ sFrontier K)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_HitMass_regular_cone_geometry
