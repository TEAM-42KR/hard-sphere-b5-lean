import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_chart_det5
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_cross_norm_sq
set_option autoImplicit false
open SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt)
open Matrix
open scoped Matrix
set_option maxHeartbeats 900000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_density_det5
    (A₀ A₁ B₀ B₁ : Fin 3 → ℝ) (u v : Pt)
    (α₀ α₁ β₀ β₁ a b z r : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 0 < z) (hr : 0 < r)
    (hA : α₀ • A₀ + α₁ • A₁ = fun i => u i)
    (hB : β₀ • B₀ + β₁ • B₁ = fun i => v i)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ‖u - v‖ = z)
    (hradius : r ^ 2 = 1 - z ^ 2 / 4) :
    let c : Fin 3 → ℝ := fun i => (cross u v) i / (z * r ^ 2)
    |Matrix.det
      ![![A₀ 0, A₀ 1, A₀ 2, -α₁ / a, 0],
        ![A₁ 0, A₁ 1, A₁ 2, α₀ / a, 0],
        ![B₀ 0, B₀ 1, B₀ 2, 0, β₁ / b],
        ![B₁ 0, B₁ 1, B₁ 2, 0, -β₀ / b],
        ![c 0, c 1, c 2, 0, 0]]| = z / (a * b) := by
  let c : Fin 3 → ℝ := fun i => (cross u v) i / (z * r ^ 2)
  change |Matrix.det
    ![![A₀ 0, A₀ 1, A₀ 2, -α₁ / a, 0],
      ![A₁ 0, A₁ 1, A₁ 2, α₀ / a, 0],
      ![B₀ 0, B₀ 1, B₀ 2, 0, β₁ / b],
      ![B₁ 0, B₁ 1, B₁ 2, 0, -β₀ / b],
      ![c 0, c 1, c 2, 0, 0]]| = z / (a * b)
  have hi : inner ℝ u v = 1 - z ^ 2 / 2 := by
    have hs := norm_sub_sq_real u v
    rw [huv, hu, hv] at hs
    nlinarith
  have hcross : ‖cross u v‖ ^ 2 = z ^ 2 * r ^ 2 := by
    rw [SphereGeom.Aux.Santalo.cross_norm_sq, hu, hv, hi, hradius]
    ring
  have htriple : Matrix.det ![fun i => u i, fun i => v i, c] =
      ‖cross u v‖ ^ 2 / (z * r ^ 2) := by
    let T : Matrix (Fin 3) (Fin 3) ℝ := ![fun i => u i, fun i => v i, c]
    change T.det = ‖cross u v‖ ^ 2 / (z * r ^ 2)
    rw [Matrix.det_fin_three T]
    simp [T, c, SphereGeom.cross, EuclideanSpace.real_norm_sq_eq,
      cross_apply, Fin.sum_univ_succ]
    ring
  have htriplez : Matrix.det ![fun i => u i, fun i => v i, c] = z := by
    rw [htriple, hcross]
    field_simp [ne_of_gt hz, ne_of_gt hr] <;> ring
  have hdet := HardSphereB5.SphericalCrofton.Aux.Coarea.incidence_chart_det5
    A₀ A₁ B₀ B₁ c α₀ α₁ β₀ β₁ (1 / a) (-1 / b)
  have hphysical : Matrix.det
      ![![A₀ 0, A₀ 1, A₀ 2, -α₁ / a, 0],
        ![A₁ 0, A₁ 1, A₁ 2, α₀ / a, 0],
        ![B₀ 0, B₀ 1, B₀ 2, 0, β₁ / b],
        ![B₁ 0, B₁ 1, B₁ 2, 0, -β₀ / b],
        ![c 0, c 1, c 2, 0, 0]] = z / (a * b) := by
    have h := hdet
    rw [hA, hB, htriplez] at h
    convert h using 1 <;> ring
  rw [hphysical, abs_of_pos (div_pos hz (mul_pos ha hb))]

