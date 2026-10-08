import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_chart_det5
import Mathlib
set_option autoImplicit false
open Matrix
open scoped Matrix

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.incidence_chart_det5 :
    ∀ (A₀ A₁ B₀ B₁ c : Fin 3 → ℝ) (α₀ α₁ β₀ β₁ s t : ℝ), Matrix.det
      ![![A₀ 0, A₀ 1, A₀ 2, -α₁ * s, 0],
        ![A₁ 0, A₁ 1, A₁ 2, α₀ * s, 0],
        ![B₀ 0, B₀ 1, B₀ 2, 0, -β₁ * t],
        ![B₁ 0, B₁ 1, B₁ 2, 0, β₀ * t],
        ![c 0, c 1, c 2, 0, 0]] =
      -(s * t) * Matrix.det ![α₀ • A₀ + α₁ • A₁, β₀ • B₀ + β₁ • B₁, c] :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_chart_det5
