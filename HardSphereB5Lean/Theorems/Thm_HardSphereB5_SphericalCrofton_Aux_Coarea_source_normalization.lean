import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_normalization
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.source_normalization :
    ∀ (f : Kern) (D u v : Pt) (hD : D ∈ LamC) (hu : u ∈ arcA D) (hv : v ∈ arcB D), (if 1 / 2 < inner ℝ u v then rhoK f (inner ℝ u v) * inner ℝ (nAv D) (cross u v) * inner ℝ (nBv D) (cross u v) else 0) /
    (HardSphereB5.SphericalCrofton.Aux.MovingArc.rA D * HardSphereB5.SphericalCrofton.Aux.MovingArc.rB D) =
  (if 0 < dist (D+u) (D+v) ∧ dist (D+u) (D+v) < 1 then
    rhoK f (1-dist (D+u) (D+v)^2/2) * inner ℝ u (NAv (D+u) (D+v)) * inner ℝ v (NBv (D+u) (D+v)) /
      (‖D‖ * ‖D-e‖ * HardSphereB5.SphericalCrofton.Aux.MovingArc.rA D * HardSphereB5.SphericalCrofton.Aux.MovingArc.rB D) else 0) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_normalization
