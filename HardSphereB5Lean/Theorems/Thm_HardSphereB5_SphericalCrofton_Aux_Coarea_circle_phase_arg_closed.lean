import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_circle_phase_arg_closed
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.circle_phase_arg_closed :
    ∀ (f : Fin 2 → Pt) (hf : Orthonormal ℝ f) (c : Pt) (r θ : ℝ) (hr : 0 < r)
    (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi)
    (hslit : phase (inner ℝ (f 0) (circlePt c (f 0) (f 1) r θ - c))
      (inner ℝ (f 1) (circlePt c (f 0) (f 1) r θ - c)) ∈ Complex.slitPlane), Complex.arg (phase (inner ℝ (f 0) (circlePt c (f 0) (f 1) r θ - c))
      (inner ℝ (f 1) (circlePt c (f 0) (f 1) r θ - c))) = θ :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_circle_phase_arg_closed
