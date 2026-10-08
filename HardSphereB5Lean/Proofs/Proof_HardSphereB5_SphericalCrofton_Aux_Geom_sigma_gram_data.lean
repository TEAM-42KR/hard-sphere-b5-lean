import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_TwoBalls_ball_iff_inner
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 2000000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_sigma_gram_data (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D) :
    let x := nAv D
    let y := nBv D
    let a := ‖D‖ / 2
    let b := ‖D - e‖ / 2
    let c := inner ℝ x y
    ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ 0 < 1 - c ^ 2 ∧ 0 < a ∧ 0 < b ∧
    0 ≤ a - c * b ∧ 0 ≤ b - c * a ∧
    (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) = (Rc ‖D‖ ‖D - e‖) ^ 2 ∧
    0 ≤ Rc ‖D‖ ‖D - e‖ ∧
    SigmaD D = {u : Pt | ‖u‖ = 1 ∧ a ≤ inner ℝ x u ∧ b ≤ inner ℝ y u} ∧
    vertsD D = {u : Pt | ‖u‖ = 1 ∧ inner ℝ x u = a ∧ inner ℝ y u = b} := by
  dsimp only
  let A := ‖D‖
  let B := ‖D - e‖
  let a := A / 2
  let b := B / 2
  let x := nAv D
  let y := nBv D
  let c := inner ℝ x y
  let t := D 0
  let k := (D 1) ^ 2 + (D 2) ^ 2
  let g := A ^ 2 + B ^ 2 - 1
  let H := (A + B + 1) * (A + B - 1) * (A - B + 1) * (-A + B + 1)
  change ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ 0 < 1 - c ^ 2 ∧ 0 < a ∧ 0 < b ∧
    0 ≤ a - c * b ∧ 0 ≤ b - c * a ∧
    (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) = (Rc A B) ^ 2 ∧
    0 ≤ Rc A B ∧ SigmaD D = _ ∧ vertsD D = _
  have he0 : e 0 = 1 := by simp [e, EuclideanSpace.single]
  have he1 : e 1 = 0 := by simp [e, EuclideanSpace.single]
  have he2 : e 2 = 0 := by simp [e, EuclideanSpace.single]
  have hcoord (v : Pt) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [PiLp.inner_apply, Fin.sum_univ_three]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hA : 0 < A := norm_pos_iff.mpr (by
    intro heq
    exact hoff 0 (by simpa using heq))
  have hB : 0 < B := norm_pos_iff.mpr (by
    intro heq
    exact hoff 1 (by simpa using sub_eq_zero.mp heq))
  have hA2 : A ^ 2 = t ^ 2 + k := by simpa only [A, t, k, add_assoc] using hcoord D
  have hB2 : B ^ 2 = (t - 1) ^ 2 + k := by
    simpa only [PiLp.sub_apply, he0, he1, he2, sub_zero, B, t, k, add_assoc] using hcoord (D - e)
  have hk : 0 < k := by
    have hk0 : 0 ≤ k := add_nonneg (sq_nonneg _) (sq_nonneg _)
    by_contra hh
    have hz : k = 0 := le_antisymm (not_lt.mp hh) hk0
    have h1 : D 1 = 0 := by nlinarith only [hz, sq_nonneg (D 1), sq_nonneg (D 2)]
    have h2 : D 2 = 0 := by nlinarith only [hz, sq_nonneg (D 1), sq_nonneg (D 2)]
    apply hoff t
    ext i
    fin_cases i <;> simp [t, he0, he1, he2, h1, h2]
  have hD0 : A ≤ 1 := by simpa [LamC, Metric.mem_closedBall, dist_zero_right, A] using hD.1
  have hD1 : B ≤ 1 := by simpa [LamC, Metric.mem_closedBall, dist_eq_norm, B] using hD.2
  have hA1 : A ^ 2 ≤ 1 := by nlinarith only [hD0, hA]
  have hB1 : B ^ 2 ≤ 1 := by nlinarith only [hD1, hB]
  have hDe : inner ℝ D e = t := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial, he0, he1, he2]
    simp [t]
  have hab : inner ℝ (-D) (e - D) = g / 2 := by
    rw [inner_neg_left, inner_sub_right, hDe, real_inner_self_eq_norm_sq]
    change -(t - A ^ 2) = g / 2
    dsimp [g]
    nlinarith only [hA2, hB2]
  have hx : ‖x‖ = 1 := by
    change ‖A⁻¹ • (-D)‖ = 1
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA)]
    exact inv_mul_cancel₀ (ne_of_gt hA)
  have hy : ‖y‖ = 1 := by
    change ‖B⁻¹ • (e - D)‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB), norm_sub_rev]
    exact inv_mul_cancel₀ (ne_of_gt hB)
  have hc : c = g / (2 * A * B) := by
    change inner ℝ (A⁻¹ • (-D)) (B⁻¹ • (e - D)) = _
    rw [real_inner_smul_left, real_inner_smul_right, hab]
    field_simp <;> ring
  have halg : 4 * A ^ 2 * B ^ 2 - g ^ 2 = 4 * k := by
    dsimp [g]
    rw [hA2, hB2]
    ring
  have hdet : (1 - c ^ 2) * (4 * A ^ 2 * B ^ 2) = 4 * k := by
    calc (1 - c ^ 2) * (4 * A ^ 2 * B ^ 2) = 4 * A ^ 2 * B ^ 2 - g ^ 2 := by
           rw [hc]
           field_simp [ne_of_gt hA, ne_of_gt hB]
           <;> ring
         _ = 4 * k := halg
  have hd : 0 < 1 - c ^ 2 := by
    have hp : 0 < 4 * A ^ 2 * B ^ 2 := mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hA)) (sq_pos_of_pos hB)
    exact (mul_pos_iff_of_pos_right hp).mp (by rw [hdet]; positivity)
  have hH : H = 4 * k := by
    calc H = 4 * A ^ 2 * B ^ 2 - g ^ 2 := by dsimp [H, g]; ring
         _ = 4 * k := halg
  have hHpos : 0 < H := by rw [hH]; positivity
  have hnum : a ^ 2 - 2 * c * a * b + b ^ 2 = 1 / 4 := by
    rw [hc]
    dsimp [a, b, g]
    field_simp [ne_of_gt hA, ne_of_gt hB]
    <;> ring
  have hq : (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) = (Rc A B) ^ 2 := by
    rw [hnum]
    unfold Rc
    rw [div_pow, Real.sq_sqrt (show 0 ≤ H from hHpos.le)]
    change (1 / 4 : ℝ) / (1 - c ^ 2) = (A * B) ^ 2 / H
    apply (div_eq_div_iff (ne_of_gt hd) (ne_of_gt hHpos)).2
    rw [hH]
    nlinarith only [hdet]
  have hac : 0 ≤ a - c * b := by
    have heq : a - c * b = (A ^ 2 - B ^ 2 + 1) / (4 * A) := by
      rw [hc]; dsimp [a, b, g]
      field_simp [ne_of_gt hA, ne_of_gt hB]
      <;> ring
    rw [heq]
    exact div_nonneg (by nlinarith only [hB1, sq_nonneg A]) (by positivity)
  have hbc : 0 ≤ b - c * a := by
    have heq : b - c * a = (B ^ 2 - A ^ 2 + 1) / (4 * B) := by
      rw [hc]; dsimp [a, b, g]
      field_simp [ne_of_gt hA, ne_of_gt hB]
      <;> ring
    rw [heq]
    exact div_nonneg (by nlinarith only [hA1, sq_nonneg B]) (by positivity)
  have hr : 0 ≤ Rc A B := div_nonneg (mul_nonneg hA.le hB.le) (Real.sqrt_nonneg _)
  have hhx (u : Pt) : inner ℝ x u = -inner ℝ D u / A := by
    simp [x, nAv, A, real_inner_smul_left, inner_neg_left, div_eq_mul_inv, mul_comm]
  have hhy (u : Pt) : inner ℝ y u = -inner ℝ (D - e) u / B := by
    change inner ℝ (B⁻¹ • (e - D)) u = _
    rw [real_inner_smul_left, ← neg_sub D e, inner_neg_left]
    ring
  have hix (u : Pt) : (a ≤ inner ℝ x u) ↔ A ^ 2 + 2 * inner ℝ D u ≤ 0 := by
    rw [hhx, le_div_iff₀ hA]
    dsimp [a]; constructor <;> intro hh <;> nlinarith only [hh]
  have hiy (u : Pt) : (b ≤ inner ℝ y u) ↔ B ^ 2 + 2 * inner ℝ (D - e) u ≤ 0 := by
    rw [hhy, le_div_iff₀ hB]
    dsimp [b]; constructor <;> intro hh <;> nlinarith only [hh]
  have hex (u : Pt) : (inner ℝ x u = a) ↔ A ^ 2 + 2 * inner ℝ D u = 0 := by
    rw [hhx, div_eq_iff (ne_of_gt hA)]
    dsimp [a]; constructor <;> intro hh <;> nlinarith only [hh]
  have hey (u : Pt) : (inner ℝ y u = b) ↔ B ^ 2 + 2 * inner ℝ (D - e) u = 0 := by
    rw [hhy, div_eq_iff (ne_of_gt hB)]
    dsimp [b]; constructor <;> intro hh <;> nlinarith only [hh]
  refine ⟨hx, hy, hd, div_pos hA (by norm_num), div_pos hB (by norm_num), hac, hbc, hq, hr, ?_, ?_⟩
  · ext u
    change (‖u‖ = 1 ∧ D + u ∈ LamC) ↔ (‖u‖ = 1 ∧ a ≤ inner ℝ x u ∧ b ≤ inner ℝ y u)
    by_cases hu : ‖u‖ = 1
    · simp only [hu, true_and, hix, hiy]
      simp only [LamC, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero]
      change (‖D + u‖ ≤ 1 ∧ ‖D + u - e‖ ≤ 1) ↔ _
      exact SphereGeom.Aux.TwoBalls.ball_iff_inner D e u hu
    · simp [hu]
  · ext u
    change (‖u‖ = 1 ∧ ‖D + u‖ = 1 ∧ dist (D + u) e = 1) ↔ (‖u‖ = 1 ∧ inner ℝ x u = a ∧ inner ℝ y u = b)
    by_cases hu : ‖u‖ = 1
    · simp only [hu, true_and, hex, hey, dist_eq_norm]
      have hn0 : ‖D + u‖ ^ 2 = A ^ 2 + 1 + 2 * inner ℝ D u := by rw [norm_add_sq_real, hu]; change A ^ 2 + 2 * inner ℝ D u + 1 ^ 2 = _; ring
      have hn1 : ‖D + u - e‖ ^ 2 = B ^ 2 + 1 + 2 * inner ℝ (D - e) u := by
        rw [show D + u - e = (D - e) + u by module, norm_add_sq_real, hu]; change B ^ 2 + 2 * inner ℝ (D - e) u + 1 ^ 2 = _; ring
      constructor
      · rintro ⟨h0, h1⟩
        constructor <;> nlinarith only [hn0, hn1, h0, h1]
      · rintro ⟨h0, h1⟩
        constructor
        · nlinarith only [hn0, h0, norm_nonneg (D + u)]
        · nlinarith only [hn1, h1, norm_nonneg (D + u - e)]
    · simp [hu]
