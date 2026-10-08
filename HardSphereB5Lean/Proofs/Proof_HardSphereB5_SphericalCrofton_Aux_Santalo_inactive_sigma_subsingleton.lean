import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_sigma_gram_data
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_inactive_sigma_subsingleton (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hr : 1 ≤ Rc ‖D‖ ‖D - e‖) : (SigmaD D).Subsingleton := by
  let x : Pt := nAv D
  let y : Pt := nBv D
  let a : ℝ := ‖D‖ / 2
  let b : ℝ := ‖D - e‖ / 2
  let c : ℝ := inner ℝ x y
  let k : ℝ := 1 - c ^ 2
  let N : ℝ := a ^ 2 - 2 * c * a * b + b ^ 2
  obtain ⟨hx, hy, hk, ha, hb, hla, hmb, hR, hR0, hSigma, hverts⟩ :=
    HardSphereB5.SphericalCrofton.Aux.Geom.sigma_gram_data D hD hoff
  change ‖x‖ = 1 at hx
  change ‖y‖ = 1 at hy
  change 0 < k at hk
  change 0 ≤ a - c * b at hla
  change 0 ≤ b - c * a at hmb
  change N / k = (Rc ‖D‖ ‖D - e‖) ^ 2 at hR
  let l : ℝ := (a - c * b) / k
  let m : ℝ := (b - c * a) / k
  let w : Pt := l • x + m • y
  have hl : 0 ≤ l := div_nonneg hla hk.le
  have hm : 0 ≤ m := div_nonneg hmb hk.le
  have hc : inner ℝ x y = c := rfl
  have hw : ‖w‖ ^ 2 = N / k := by
    dsimp only [w]
    rw [norm_add_sq_real, norm_smul, norm_smul, hx, hy]
    simp only [mul_one, Real.norm_eq_abs, sq_abs, real_inner_smul_left,
      real_inner_smul_right, hc]
    change l ^ 2 + 2 * (m * (l * c)) + m ^ 2 = N / k
    have hk0 : 1 - c ^ 2 ≠ 0 := ne_of_gt hk
    dsimp only [l, m, N, k]
    field_simp [hk0]
    <;> ring
  have hlin : l * a + m * b = N / k := by
    dsimp only [l, m, N, k]
    field_simp [ne_of_gt hk]
    <;> ring
  have hNR : 1 ≤ N / k := by
    rw [hR]
    nlinarith
  have hpoint (u : Pt) (hu : u ∈ SigmaD D) : u = w := by
    rw [hSigma] at hu
    obtain ⟨hun, hua, hub⟩ := hu
    change ‖u‖ = 1 at hun
    change a ≤ inner ℝ x u at hua
    change b ≤ inner ℝ y u at hub
    have hi : N / k ≤ inner ℝ w u := by
      rw [← hlin]
      dsimp only [w]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      exact add_le_add (mul_le_mul_of_nonneg_left hua hl)
        (mul_le_mul_of_nonneg_left hub hm)
    have hs : ‖u - w‖ ^ 2 = 1 + N / k - 2 * inner ℝ w u := by
      rw [norm_sub_sq_real, hun, hw, real_inner_comm u w]
      ring
    have hn : ‖u - w‖ = 0 := by
      nlinarith [norm_nonneg (u - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  intro u hu v hv
  exact (hpoint u hu).trans (hpoint v hv).symm
