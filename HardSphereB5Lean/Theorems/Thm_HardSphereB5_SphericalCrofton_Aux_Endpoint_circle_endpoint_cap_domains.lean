import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_cap_domains
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.circle_endpoint_cap_domains :
    ∀ (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)), ∃ (C : CircleEndpointAtlas) (F : Set Pt),
      F.Finite ∧
      C.c 0 = (-(1/2 : ℝ)) • D ∧ C.c 1 = (1/2 : ℝ) • (e-D) ∧
      C.r 0 = Real.sqrt (1 - ‖D‖^2/4) ∧ C.r 1 = Real.sqrt (1 - ‖D-e‖^2/4) ∧
      (∀ i, Orthonormal ℝ (C.frame i)) ∧ (∀ i, 0 < C.r i) ∧
      (∀ i, 0 ≤ C.T i) ∧ (∀ i, C.T i ≤ 2*Real.pi) ∧
      (∀ i : Fin 2, atlasCircle C i '' Set.Ioo 0 (C.T i) =
        (if i = 0 then arcA D else arcB D) \ F) ∧
      arcA D ∩ arcB D ⊆ F ∧
      sFrontier (SigmaD D) \ F = (arcA D ∪ arcB D) \ F ∧
      (∀ (i : Fin 2) t, t ∈ Set.Ioo 0 (C.T i) →
        HasDerivAt (atlasCircle C i)
          (if i = 0 then cross (nAv D) (atlasCircle C i t)
           else -cross (nBv D) (atlasCircle C i t)) t ∧
        ‖cross (if i = 0 then nAv D else nBv D) (atlasCircle C i t)‖ = C.r i) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_cap_domains
