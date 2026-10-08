import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_density_det5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt)
open Matrix
open scoped Matrix

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.incidence_density_det5 :
    ∀ (A₀ A₁ B₀ B₁ : Fin 3 → ℝ) (u v : Pt)
    (α₀ α₁ β₀ β₁ a b z r : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 0 < z) (hr : 0 < r)
    (hA : α₀ • A₀ + α₁ • A₁ = fun i => u i)
    (hB : β₀ • B₀ + β₁ • B₁ = fun i => v i)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ‖u - v‖ = z)
    (hradius : r ^ 2 = 1 - z ^ 2 / 4),
    let c : Fin 3 → ℝ := fun i => (cross u v) i / (z * r ^ 2)
    |Matrix.det
      ![![A₀ 0, A₀ 1, A₀ 2, -α₁ / a, 0],
        ![A₁ 0, A₁ 1, A₁ 2, α₀ / a, 0],
        ![B₀ 0, B₀ 1, B₀ 2, 0, β₁ / b],
        ![B₁ 0, B₁ 1, B₁ 2, 0, -β₀ / b],
        ![c 0, c 1, c 2, 0, 0]]| = z / (a * b) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_density_det5
