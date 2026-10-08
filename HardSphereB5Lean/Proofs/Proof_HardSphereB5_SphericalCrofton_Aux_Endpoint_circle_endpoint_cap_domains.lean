import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import Mathlib
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
private theorem HardSphereB5.SphericalCrofton.sigma_axis_cases :
    (∀ t : ℝ, 0 < t → t < 1 → SigmaD (t • e) = ∅) ∧
      (SigmaD 0 = cap e (1 / 2) ∧ arcA 0 = ∅ ∧ arcB 0 = {u | ‖u‖ = 1 ∧ inner ℝ e u = 1 / 2}) ∧
      (SigmaD e = cap (-e) (1 / 2) ∧ arcB e = ∅ ∧
        arcA e = {u | ‖u‖ = 1 ∧ inner ℝ (-e) u = 1 / 2}) := by
  have he : ‖e‖ = 1 := by simp [HardSphereB5.Lean.e]
  have he0 : e ≠ 0 := by
    intro h
    simpa [h] using he
  have hle (v : Pt) : ‖v‖ ≤ 1 ↔ ‖v‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ (norm_nonneg v) (zero_le_one : (0 : ℝ) ≤ 1)).symm
  have heq (v : Pt) : ‖v‖ = 1 ↔ ‖v‖ ^ 2 = 1 := by
    simpa only [one_pow] using (sq_eq_sq₀ (norm_nonneg v) (zero_le_one : (0 : ℝ) ≤ 1)).symm
  have hsub (u : Pt) (hu : ‖u‖ = 1) :
      ‖u - e‖ ^ 2 = 2 - 2 * inner ℝ e u := by
    rw [norm_sub_sq_real, hu, he, real_inner_comm e u]
    ring
  have hadd (u : Pt) (hu : ‖u‖ = 1) :
      ‖e + u‖ ^ 2 = 2 + 2 * inner ℝ e u := by
    rw [norm_add_sq_real, hu, he]
    ring
  have hmem (D u : Pt) :
      u ∈ SigmaD D ↔ ‖u‖ = 1 ∧ ‖D + u‖ ≤ 1 ∧ ‖D + u - e‖ ≤ 1 := by
    simp only [SigmaD, LamC, Set.mem_setOf_eq, Set.mem_inter_iff,
      Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero]
  have hzero (u : Pt) :
      u ∈ SigmaD 0 ↔ ‖u‖ = 1 ∧ (1 / 2 : ℝ) ≤ inner ℝ e u := by
    rw [hmem]
    simp only [zero_add]
    constructor
    · rintro ⟨hu, _, hb⟩
      have hb2 := (hle (u - e)).mp hb
      exact ⟨hu, by nlinarith [hsub u hu]⟩
    · rintro ⟨hu, hi⟩
      refine ⟨hu, by simp [hu], (hle (u - e)).mpr ?_⟩
      nlinarith [hsub u hu]
  have hendpoint (u : Pt) :
      u ∈ SigmaD e ↔ ‖u‖ = 1 ∧ (1 / 2 : ℝ) ≤ inner ℝ (-e) u := by
    rw [hmem]
    simp only [add_sub_cancel_left, inner_neg_left]
    constructor
    · rintro ⟨hu, ha, _⟩
      have ha2 := (hle (e + u)).mp ha
      exact ⟨hu, by nlinarith [hadd u hu]⟩
    · rintro ⟨hu, hi⟩
      refine ⟨hu, (hle (e + u)).mpr ?_, by simp [hu]⟩
      nlinarith [hadd u hu]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro t ht ht1
    ext u
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hu
    obtain ⟨hu, ha, hb⟩ := (hmem (t • e) u).mp hu
    have hsmul (s : ℝ) : ‖s • e‖ ^ 2 = s ^ 2 := by
      simp only [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
    have ha2 := (hle (t • e + u)).mp ha
    have hb2 := (hle (t • e + u - e)).mp hb
    have haexp : ‖t • e + u‖ ^ 2 = t ^ 2 + 2 * t * inner ℝ e u + 1 := by
      rw [norm_add_sq_real, hsmul, real_inner_smul_left, hu]
      ring
    have hv : t • e + u - e = (t - 1) • e + u := by
      rw [sub_smul, one_smul]
      abel
    have hbexp : ‖t • e + u - e‖ ^ 2 = (t - 1) ^ 2 + 2 * (t - 1) * inner ℝ e u + 1 := by
      rw [hv, norm_add_sq_real, hsmul, real_inner_smul_left, hu]
      ring
    have hineg : inner ℝ e u < 0 := by
      by_contra h
      have hprod : 0 ≤ t * inner ℝ e u := mul_nonneg ht.le (le_of_not_gt h)
      nlinarith [haexp]
    have hprod : 0 ≤ (t - 1) * inner ℝ e u :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hineg.le
    nlinarith [hbexp]
  · ext u
    exact hzero u
  · simp [arcA]
  · ext u
    simp only [arcB, if_neg (Ne.symm he0), Set.mem_setOf_eq,
      zero_add, dist_eq_norm, hzero]
    constructor
    · rintro ⟨⟨hu, _⟩, hd⟩
      have hd2 := (heq (u - e)).mp hd
      exact ⟨hu, by nlinarith [hsub u hu]⟩
    · rintro ⟨hu, hi⟩
      refine ⟨⟨hu, by linarith⟩, (heq (u - e)).mpr ?_⟩
      nlinarith [hsub u hu]
  · ext u
    exact hendpoint u
  · simp [arcB]
  · ext u
    simp only [arcA, if_neg he0, Set.mem_setOf_eq, hendpoint, inner_neg_left]
    constructor
    · rintro ⟨⟨hu, _⟩, hd⟩
      have hd2 := (heq (e + u)).mp hd
      exact ⟨hu, by nlinarith [hadd u hu]⟩
    · rintro ⟨hu, hi⟩
      refine ⟨⟨hu, by linarith⟩, (heq (e + u)).mpr ?_⟩
      nlinarith [hadd u hu]

end

section
open SphereGeom MeasureTheory

private theorem SphereGeom.Aux.TwoBalls.ball_iff_inner (D E u : E3) (hu : ‖u‖ = 1) :
    (‖D + u‖ ≤ 1 ∧ ‖D + u - E‖ ≤ 1) ↔
      (‖D‖ ^ 2 + 2 * inner ℝ D u ≤ 0 ∧
       ‖D - E‖ ^ 2 + 2 * inner ℝ (D - E) u ≤ 0) := by
  have aux (v : E3) : ‖v + u‖ ≤ 1 ↔ ‖v‖ ^ 2 + 2 * inner ℝ v u ≤ 0 := by
    have hh := norm_add_sq_real v u
    rw [hu] at hh
    constructor
    · intro hv
      nlinarith [norm_nonneg (v + u)]
    · intro hv
      nlinarith [norm_nonneg (v + u)]
  have heq : D + u - E = (D - E) + u := by abel
  rw [heq, aux D, aux (D - E)]
end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 2000000

private theorem HardSphereB5.SphericalCrofton.Aux.Geom.sigma_gram_data (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D) :
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
end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

private theorem HardSphereB5.SphericalCrofton.Aux.Geom.gram_obstruction (x y : Pt) (a b c : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = c)
    (hd : 0 < 1 - c ^ 2) (ha : 0 ≤ a - c * b) (hb : 0 ≤ b - c * a) :
    let q := (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2)
    let p := ((a - c * b) / (1 - c ^ 2)) • x + ((b - c * a) / (1 - c ^ 2)) • y
    let K := {u : Pt | ‖u‖ = 1 ∧ a ≤ inner ℝ x u ∧ b ≤ inner ℝ y u}
    (K.Nonempty → q ≤ 1) ∧ (q = 1 → K = {p}) ∧ (1 < q → K = ∅) := by
  dsimp only
  let q := (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2)
  let α := (a - c * b) / (1 - c ^ 2)
  let β := (b - c * a) / (1 - c ^ 2)
  let p : Pt := α • x + β • y
  let K := {u : Pt | ‖u‖ = 1 ∧ a ≤ inner ℝ x u ∧ b ≤ inner ℝ y u}
  change (K.Nonempty → q ≤ 1) ∧ (q = 1 → K = {p}) ∧ (1 < q → K = ∅)
  have hα : 0 ≤ α := div_nonneg ha hd.le
  have hβ : 0 ≤ β := div_nonneg hb hd.le
  have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyy : inner ℝ y y = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hyx : inner ℝ y x = c := by rw [real_inner_comm, hxy]
  have hpx : inner ℝ x p = a := by
    dsimp [p]
    rw [inner_add_right, inner_smul_right, inner_smul_right, hxx, hxy]
    dsimp [α, β]
    field_simp
    <;> nlinarith [ne_of_gt hd]
  have hpy : inner ℝ y p = b := by
    dsimp [p]
    rw [inner_add_right, inner_smul_right, inner_smul_right, hyx, hyy]
    dsimp [α, β]
    field_simp
    <;> nlinarith [ne_of_gt hd]
  have hpp : inner ℝ p p = q := by
    dsimp [p]
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    change α * inner ℝ x p + β * inner ℝ y p = q
    rw [hpx, hpy]
    dsimp [α, β, q]
    field_simp
    <;> nlinarith [ne_of_gt hd]
  have hbound : ∀ u ∈ K, q ≤ 1 ∧ (q = 1 → u = p) := by
    intro u hu
    have hpu : q ≤ inner ℝ p u := by
      have hpq : α * a + β * b = q := by
        rw [← hpp]
        change α * a + β * b = inner ℝ (α • x + β • y) p
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hpx, hpy]
      dsimp [p]
      rw [inner_add_left, inner_smul_left, inner_smul_left, ← hpq]
      exact add_le_add (mul_le_mul_of_nonneg_left hu.2.1 hα) (mul_le_mul_of_nonneg_left hu.2.2 hβ)
    have hnorm : ‖u - p‖ ^ 2 = 1 + q - 2 * inner ℝ p u := by
      rw [norm_sub_sq_real, hu.1, ← real_inner_self_eq_norm_sq, hpp, real_inner_comm]
      ring
    have hz := sq_nonneg ‖u - p‖
    refine ⟨by nlinarith, ?_⟩
    intro hq
    have heq : ‖u - p‖ = 0 := by nlinarith [norm_nonneg (u - p)]
    exact sub_eq_zero.mp (norm_eq_zero.mp heq)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    exact (hbound u hu).1
  · intro hq
    ext u
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hu
      exact (hbound u hu).2 hq
    · rintro rfl
      refine ⟨?_, hpx.ge, hpy.ge⟩
      have hp1 : ‖p‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hpp, hq]
      nlinarith [norm_nonneg p]
  · intro hq
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact (not_le_of_gt hq) (hbound u hu).1
end

section
open SphereGeom
open HardSphereB5.Lean (Pt)

private theorem HardSphereB5.SphericalCrofton.Aux.Geom.cross_identities (x y u : Pt) :
    inner ℝ x (cross x y) = 0 ∧ inner ℝ y (cross x y) = 0 ∧
    inner ℝ (cross x y) (cross x y) = inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2 ∧
    (inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2) • u =
      (inner ℝ y y * inner ℝ x u - inner ℝ x y * inner ℝ y u) • x +
      (inner ℝ x x * inner ℝ y u - inner ℝ x y * inner ℝ x u) • y +
      (inner ℝ (cross x y) u) • cross x y := by
  have hi (v w : Pt) : inner ℝ v w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_three]
    <;> ring
  have hc (v w : Pt) : cross v w = WithLp.toLp 2
      ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hi]
    simp [hc]; ring
  · simp only [hi]
    simp [hc]; ring
  · simp only [hi]
    simp [hc]; ring
  · simp only [hi]
    ext i
    fin_cases i <;> simp [hc] <;> ring
end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 2000000

private theorem HardSphereB5.SphericalCrofton.Aux.Geom.gram_vertices (x y : Pt) (a b c : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = c)
    (hd : 0 < 1 - c ^ 2)
    (hq : (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) < 1) :
    ∃ V W : Pt, V ≠ W ∧ {u : Pt | ‖u‖ = 1 ∧ inner ℝ x u = a ∧ inner ℝ y u = b} = {V, W} := by
  let d := 1 - c ^ 2
  let q := (a ^ 2 - 2 * c * a * b + b ^ 2) / d
  let α := (a - c * b) / d
  let β := (b - c * a) / d
  let p : Pt := α • x + β • y
  let z := cross x y
  let r := √((1 - q) / d)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyy : inner ℝ y y = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hyx : inner ℝ y x = c := by rw [real_inner_comm, hxy]
  have hz := Aux.Geom.cross_identities x y p
  have hxz : inner ℝ x z = 0 := hz.1
  have hyz : inner ℝ y z = 0 := hz.2.1
  have hzz : inner ℝ z z = d := by simpa only [z, hxx, hyy, hxy, one_mul, d] using hz.2.2.1
  have hpx : inner ℝ x p = a := by
    dsimp [p]
    rw [inner_add_right, inner_smul_right, inner_smul_right, hxx, hxy]
    dsimp [α, β]
    field_simp
    <;> dsimp [d] at *
    <;> nlinarith [ne_of_gt hd]
  have hpy : inner ℝ y p = b := by
    dsimp [p]
    rw [inner_add_right, inner_smul_right, inner_smul_right, hyx, hyy]
    dsimp [α, β]
    field_simp
    <;> dsimp [d] at *
    <;> nlinarith [ne_of_gt hd]
  have hpp : inner ℝ p p = q := by
    change inner ℝ (α • x + β • y) p = q
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hpx, hpy]
    dsimp [α, β, q]
    field_simp
    <;> dsimp [d] at *
    <;> nlinarith [ne_of_gt hd]
  have hpz : inner ℝ p z = 0 := by simp [p, inner_add_left, real_inner_smul_left, hxz, hyz]
  have hzp : inner ℝ z p = 0 := by rw [real_inner_comm, hpz]
  have hr2 : r ^ 2 = (1 - q) / d := Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hq.le) hd.le)
  have hrd : r ^ 2 * d = 1 - q := by rw [hr2]; exact div_mul_cancel₀ _ hd0
  have hr : 0 < r := Real.sqrt_pos.2 (div_pos (sub_pos.mpr hq) hd)
  have hpadd (t : ℝ) : ‖p + t • z‖ ^ 2 = q + t ^ 2 * d := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hpp, hpz, hzp, hzz]
    ring
  have hmem (t : ℝ) (ht : t ^ 2 = r ^ 2) :
      ‖p + t • z‖ = 1 ∧ inner ℝ x (p + t • z) = a ∧ inner ℝ y (p + t • z) = b := by
    refine ⟨?_, ?_, ?_⟩
    · have hnorm := hpadd t
      rw [ht] at hnorm
      nlinarith [norm_nonneg (p + t • z)]
    · simp [inner_add_right, inner_smul_right, hpx, hxz]
    · simp [inner_add_right, inner_smul_right, hpy, hyz]
  refine ⟨p + r • z, p + (-r) • z, ?_, ?_⟩
  · intro heq
    have hi := congrArg (fun u : Pt => inner ℝ z u) heq
    simp only [inner_add_right, real_inner_smul_right, hzp, hzz, zero_add] at hi
    nlinarith
  · ext u
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu, hux, huy⟩
      let t := inner ℝ z u / d
      have hid := (Aux.Geom.cross_identities x y u).2.2.2
      rw [hxx, hyy, hxy, hux, huy] at hid
      have hup : u = p + t • z := by
        calc u = d⁻¹ • (d • u) := by simp [smul_smul, hd0]
             _ = p + t • z := by
               rw [show d • u = (a - c * b) • x + (b - c * a) • y + inner ℝ z u • z by simpa [d, z] using hid]
               simp [p, α, β, t, smul_add, smul_smul, div_eq_mul_inv, mul_comm]
      have hnorm := hpadd t
      rw [← hup, hu] at hnorm
      have ht2 : t ^ 2 = r ^ 2 := by nlinarith
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp ht2 with ht | ht
      · left; simpa [ht] using hup
      · right; simpa [ht] using hup
    · rintro (rfl | rfl)
      · exact hmem r rfl
      · exact hmem (-r) (by ring)
end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

private theorem HardSphereB5.SphericalCrofton.Aux.Geom.gram_projection (x y : Pt) (a b c : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = c) (hd : 0 < 1 - c ^ 2) :
    let p := ((a - c * b) / (1 - c ^ 2)) • x + ((b - c * a) / (1 - c ^ 2)) • y
    inner ℝ x p = a ∧ inner ℝ y p = b ∧
    ‖p‖ ^ 2 = (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) := by
  dsimp only
  let q := (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2)
  let α := (a - c * b) / (1 - c ^ 2)
  let β := (b - c * a) / (1 - c ^ 2)
  let p : Pt := α • x + β • y
  have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyy : inner ℝ y y = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hyx : inner ℝ y x = c := by rw [real_inner_comm, hxy]
  have hpx : inner ℝ x p = a := by
    dsimp [p]
    rw [inner_add_right, inner_smul_right, inner_smul_right, hxx, hxy]
    dsimp [α, β]
    field_simp
    <;> nlinarith [ne_of_gt hd]
  have hpy : inner ℝ y p = b := by
    dsimp [p]
    rw [inner_add_right, inner_smul_right, inner_smul_right, hyx, hyy]
    dsimp [α, β]
    field_simp
    <;> nlinarith [ne_of_gt hd]
  have hpp : inner ℝ p p = q := by
    dsimp [p]
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    change α * inner ℝ x p + β * inner ℝ y p = q
    rw [hpx, hpy]
    dsimp [α, β, q]
    field_simp
    <;> nlinarith [ne_of_gt hd]
  exact ⟨hpx, hpy, by rw [← real_inner_self_eq_norm_sq]; exact hpp⟩
end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

private theorem HardSphereB5.SphericalCrofton.Aux.Geom.strict_cap_interior (x y u : Pt) (a b : ℝ)
    (hu : ‖u‖ = 1) (hx : a < inner ℝ x u) (hy : b < inner ℝ y u) :
    u ∈ sInterior {v : Pt | ‖v‖ = 1 ∧ a ≤ inner ℝ x v ∧ b ≤ inner ℝ y v} := by
  let us : Metric.sphere (0 : Pt) 1 := ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu⟩
  have hc1 : Continuous (fun v : Metric.sphere (0 : Pt) 1 => inner ℝ x (v : Pt)) := continuous_const.inner continuous_subtype_val
  have hc2 : Continuous (fun v : Metric.sphere (0 : Pt) 1 => inner ℝ y (v : Pt)) := continuous_const.inner continuous_subtype_val
  have hopen : IsOpen {v : Metric.sphere (0 : Pt) 1 | a < inner ℝ x (v : Pt) ∧ b < inner ℝ y (v : Pt)} :=
    (isOpen_lt continuous_const hc1).inter (isOpen_lt continuous_const hc2)
  have hsub : {v : Metric.sphere (0 : Pt) 1 | a < inner ℝ x (v : Pt) ∧ b < inner ℝ y (v : Pt)} ⊆
      (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' {v : Pt | ‖v‖ = 1 ∧ a ≤ inner ℝ x v ∧ b ≤ inner ℝ y v} := by
    intro v hv
    refine ⟨?_, hv.1.le, hv.2.le⟩
    simpa [Metric.mem_sphere, dist_zero_right] using v.property
  refine ⟨us, interior_mono hsub ?_, rfl⟩
  rw [hopen.interior_eq]
  exact ⟨hx, hy⟩
end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

private theorem HardSphereB5.SphericalCrofton.Aux.Geom.gram_interior (x y : Pt) (a b c : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = c) (hd : 0 < 1 - c ^ 2)
    (ha : 0 < a) (hb : 0 < b)
    (hq : (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) < 1) :
    (sInterior {u : Pt | ‖u‖ = 1 ∧ a ≤ inner ℝ x u ∧ b ≤ inner ℝ y u}).Nonempty := by
  let p := ((a - c * b) / (1 - c ^ 2)) • x + ((b - c * a) / (1 - c ^ 2)) • y
  have hp := Aux.Geom.gram_projection x y a b c hx hy hxy hd
  change inner ℝ x p = a ∧ inner ℝ y p = b ∧ ‖p‖ ^ 2 = _ at hp
  have hp0 : p ≠ 0 := by intro heq; simp [heq] at hp; linarith [hp.1]
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hn1 : ‖p‖ < 1 := by nlinarith [hp.2.2]
  have hinv : 1 < ‖p‖⁻¹ := (one_lt_inv₀ hn).mpr hn1
  let u := ‖p‖⁻¹ • p
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), ne_of_gt hn]
  have hux : a < inner ℝ x u := by
    simp only [u, real_inner_smul_right, hp.1]
    nlinarith
  have huy : b < inner ℝ y u := by
    simp only [u, real_inner_smul_right, hp.2.1]
    nlinarith
  exact ⟨u, Aux.Geom.strict_cap_interior x y u a b hu hux huy⟩
end

section
open SphereGeom MeasureTheory

private theorem SphereGeom.Aux.SurfaceArea.interior_pos (A : Set E3) (hA : MeasurableSet A)
    (hi : (interior ((Subtype.val : Metric.sphere (0 : E3) 1 → E3) ⁻¹' A)).Nonempty) :
    0 < (dOmega A).toReal := by
  unfold dOmega sphereMeasure
  rw [Measure.map_apply (by fun_prop) hA]
  have hp : 0 < (volume : Measure E3).toSphere
      ((fun u : Metric.sphere (0 : E3) 1 => (0 : E3) + (u : E3)) ⁻¹' A) := by
    simpa only [zero_add] using
      (lt_of_lt_of_le
        (isOpen_interior.measure_pos (μ := (volume : Measure E3).toSphere) hi)
        (measure_mono interior_subset))
  exact ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)
end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

private theorem HardSphereB5.SphericalCrofton.sigma_support (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D) :
    (Rc ‖D‖ ‖D - e‖ < 1 → 0 < sArea (SigmaD D) ∧ ∃ V W, V ≠ W ∧ vertsD D = {V, W}) ∧
      (Rc ‖D‖ ‖D - e‖ = 1 → ∃ V, SigmaD D = {V}) ∧
      (1 < Rc ‖D‖ ‖D - e‖ → SigmaD D = ∅) := by
  let x := nAv D
  let y := nBv D
  let a := ‖D‖ / 2
  let b := ‖D - e‖ / 2
  let c := inner ℝ x y
  obtain ⟨hx, hy, hd, ha, hb, hac, hbc, hq, hr, hK, hV⟩ := Aux.Geom.sigma_gram_data D hD hoff
  change ‖x‖ = 1 at hx
  change ‖y‖ = 1 at hy
  change 0 < 1 - c ^ 2 at hd
  change 0 < a at ha
  change 0 < b at hb
  change 0 ≤ a - c * b at hac
  change 0 ≤ b - c * a at hbc
  change (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) = _ at hq
  change SigmaD D = {u : Pt | ‖u‖ = 1 ∧ a ≤ inner ℝ x u ∧ b ≤ inner ℝ y u} at hK
  change vertsD D = {u : Pt | ‖u‖ = 1 ∧ inner ℝ x u = a ∧ inner ℝ y u = b} at hV
  have hxy : inner ℝ x y = c := Eq.refl c
  have hobs := Aux.Geom.gram_obstruction x y a b c hx hy hxy hd hac hbc
  refine ⟨?_, ?_, ?_⟩
  · intro hlt
    have hq1 : (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) < 1 := by rw [hq]; nlinarith
    constructor
    · have hi := Aux.Geom.gram_interior x y a b c hx hy hxy hd ha hb hq1
      rw [← hK] at hi
      have hcl : IsClosed (SigmaD D) := by
        rw [hK]
        have hcx : Continuous (fun u : Pt => inner ℝ x u) := continuous_const.inner continuous_id
        have hcy : Continuous (fun u : Pt => inner ℝ y u) := continuous_const.inner continuous_id
        exact (isClosed_eq continuous_norm continuous_const).inter
          ((isClosed_le continuous_const hcx).inter (isClosed_le continuous_const hcy))
      apply SphereGeom.Aux.SurfaceArea.interior_pos _ hcl.measurableSet
      exact Set.image_nonempty.mp hi
    · rw [hV]
      exact Aux.Geom.gram_vertices x y a b c hx hy hxy hd hq1
  · intro heq
    refine ⟨((a - c * b) / (1 - c ^ 2)) • x + ((b - c * a) / (1 - c ^ 2)) • y, ?_⟩
    rw [hK]
    apply hobs.2.1
    rw [hq, heq]
    norm_num
  · intro hgt
    rw [hK]
    apply hobs.2.2
    rw [hq]
    nlinarith
end

section
open MeasureTheory SphereGeom
private theorem SphereGeom.exists_measurable_frame : ∃ F₁ F₂ : E3 → E3, Measurable F₁ ∧ Measurable F₂ ∧
    ∀ p, ‖p‖ = 1 → Orthonormal ℝ ![F₁ p, F₂ p, p] := by
  let r : E3 → ℝ := fun p => Real.sqrt (p 0 ^ 2 + p 1 ^ 2)
  let F₁ : E3 → E3 := fun p => if p 0 ^ 2 + p 1 ^ 2 = 0 then WithLp.toLp 2 ![1,0,0]
    else WithLp.toLp 2 ![-p 1 / r p, p 0 / r p, 0]
  let F₂ : E3 → E3 := fun p => if p 0 ^ 2 + p 1 ^ 2 = 0 then WithLp.toLp 2 ![0,1,0]
    else WithLp.toLp 2 ![-p 2 * p 0 / r p, -p 2 * p 1 / r p, r p]
  have hm : Measurable (fun p : E3 => p 0 ^ 2 + p 1 ^ 2) := by fun_prop
  have mr : Measurable r := by dsimp [r]; fun_prop
  have hms : MeasurableSet {p : E3 | p 0 ^ 2 + p 1 ^ 2 = 0} := hm (measurableSet_singleton 0)
  refine ⟨F₁, F₂, ?_, ?_, ?_⟩
  · apply Measurable.ite hms
    · fun_prop
    · apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
      apply measurable_pi_iff.mpr
      intro i; fin_cases i <;> simp [r] <;> fun_prop
  · apply Measurable.ite hms
    · fun_prop
    · apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
      apply measurable_pi_iff.mpr
      intro i; fin_cases i <;> simp [r] <;> fun_prop
  · intro p hp
    have hp2 : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1 := by
      simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, hp, add_assoc] using
        (EuclideanSpace.real_norm_sq_eq p).symm
    have hr2 : r p ^ 2 = p 0 ^ 2 + p 1 ^ 2 := Real.sq_sqrt (by positivity)
    apply orthonormal_iff_ite.mpr
    intro i j
    simp only [PiLp.inner_apply]
    by_cases h : p 0 ^ 2 + p 1 ^ 2 = 0
    · have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
      have h2 : p 2 ^ 2 = 1 := by nlinarith
      fin_cases i <;> fin_cases j <;>
        simp [F₁, F₂, h, PiLp.inner_apply, Fin.sum_univ_succ, h0, h1, ← sq, h2]
    · have hr0 : r p ≠ 0 := by intro hh; rw [hh] at hr2; simp at hr2; exact h hr2.symm
      fin_cases i <;> fin_cases j <;>
        simp [F₁, F₂, h, PiLp.inner_apply, Fin.sum_univ_succ]
      all_goals field_simp [hr0]
      all_goals nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2),
        congrArg (fun a : ℝ => p 2 * a) hr2]
end

section
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom
open HardSphereB5.SphericalCrofton.Aux.MovingArc
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem W3CapReuse12_cross_norm_sq_native (a b : Pt) :
    ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - inner ℝ a b ^ 2 := by
  simp [SphereGeom.cross, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
    cross_apply, Fin.sum_univ_succ]
  ring

private theorem W3CapReuse12_cross_inner_first (a b : Pt) : inner ℝ a (cross a b) = 0 := by
  simp [SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
  ring

private theorem W3CapReuse12_cross_inner_second (a b : Pt) : inner ℝ b (cross a b) = 0 := by
  simp [SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
  ring

private theorem W3CapReuse12_axisA_facts (D : Pt) (hoff : offAxis D) :
    D ≠ 0 ∧ ‖nAv D‖ = 1 ∧ rawA D ≠ 0 ∧
      inner ℝ (nAv D) (rawA D) = 0 := by
  have hD : D ≠ 0 := by
    intro hd
    exact hoff 0 (by simpa using hd)
  have hn : ‖nAv D‖ = 1 := by
    simp [nAv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg D),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hD)]
  have horth : inner ℝ (nAv D) (rawA D) = 0 := by
    simp only [rawA, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  have he : ‖(e : Pt)‖ = 1 := by simp [e]
  have hraw : rawA D ≠ 0 := by
    intro hr
    have heq : e = (inner ℝ (nAv D) e) • nAv D := sub_eq_zero.mp hr
    have hcoeff : inner ℝ (nAv D) e ≠ 0 := by
      intro hc
      rw [hc, zero_smul] at heq
      have hbad := congrArg norm heq
      rw [he, norm_zero] at hbad
      norm_num at hbad
    have hDaxis : D = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) • e := by
      calc
        D = (-‖D‖) • nAv D := by
          simp [nAv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hD)]
        _ = ((-‖D‖ * (inner ℝ (nAv D) e)⁻¹) * inner ℝ (nAv D) e) • nAv D := by
          rw [mul_assoc, inv_mul_cancel₀ hcoeff, mul_one]
        _ = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) •
            ((inner ℝ (nAv D) e) • nAv D) := by rw [smul_smul]
        _ = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) • e := by rw [← heq]
    exact hoff _ hDaxis
  exact ⟨hD, hn, hraw, horth⟩

private theorem W3CapReuse12_frameProof (D : Pt) (hoff : offAxis D) : Orthonormal ℝ (EA D) := by
  rcases W3CapReuse12_axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  have hf : ‖unitDir (rawA D)‖ = 1 := by
    simp [unitDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (rawA D)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]
  have hnf : inner ℝ (nAv D) (unitDir (rawA D)) = 0 := by
    rw [unitDir, real_inner_smul_right, ho, mul_zero]
  have hc : ‖cross (nAv D) (unitDir (rawA D))‖ ^ 2 = 1 := by
    rw [W3CapReuse12_cross_norm_sq_native, hn, hf, hnf]
    norm_num
  have hf0 : inner ℝ (unitDir (rawA D)) (cross (nAv D) (unitDir (rawA D))) = 0 :=
    W3CapReuse12_cross_inner_second _ _
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [EA, real_inner_self_eq_norm_sq, hf, hc, hf0, real_inner_comm]

private theorem W3CapReuse12_fullCircleImage (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁, v₂, p]) :
    circlePt 0 v₁ v₂ 1 '' Set.Icc (-Real.pi) Real.pi = greatCircle p := by
  let e : Fin 3 → E3 := ![v₁, v₂, p]
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range e) := by
    apply Eq.ge
    apply hv.linearIndependent.span_eq_top_of_card_eq_finrank
    simp [E3]
  let b : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk hv hspan
  have hb (i : Fin 3) : b i = e i := by simp [b, e]
  have hb0 : b 0 = v₁ := by simp [hb, e]
  have hb1 : b 1 = v₂ := by simp [hb, e]
  have hb2 : b 2 = p := by simp [hb, e]
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · have hc : circlePt 0 v₁ v₂ 1 t = b.repr.symm (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0]) := by
        rw [← b.sum_repr_symm]
        simp [Fin.sum_univ_succ, hb0, hb1, hb2, circlePt]
      rw [hc, b.repr.symm.norm_map]
      have hs : ‖(WithLp.toLp 2 ![Real.cos t, Real.sin t, 0] : E3)‖ ^ 2 = 1 := by
        simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Real.cos_sq_add_sin_sq]
      nlinarith [norm_nonneg (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0] : E3)]
    · have h1 : inner ℝ p v₁ = 0 := by simpa [e] using hv.inner_eq_zero (show (2 : Fin 3) ≠ 0 by decide)
      have h2 : inner ℝ p v₂ = 0 := by simpa [e] using hv.inner_eq_zero (show (2 : Fin 3) ≠ 1 by decide)
      simp [circlePt, inner_add_right, inner_smul_right, h1, h2]
  · rintro ⟨hu, hup⟩
    have hpcoord : b.repr u 2 = 0 := by simpa [b.repr_apply_apply, hb2] using hup
    have hnorm : b.repr u 0 ^ 2 + b.repr u 1 ^ 2 = 1 := by
      have h : ‖b.repr u‖ ^ 2 = 1 := by rw [b.repr.norm_map, hu]; norm_num
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simpa [Fin.sum_univ_succ, hpcoord] using h
    let z : ℂ := ⟨b.repr u 0, b.repr u 1⟩
    have hzn : ‖z‖ = 1 := by
      have h : ‖z‖ ^ 2 = 1 := by
        rw [Complex.sq_norm]
        simpa [Complex.normSq, z, pow_two] using hnorm
      nlinarith [norm_nonneg z]
    have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; norm_num at hzn
    refine ⟨z.arg, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
    have hc : Real.cos z.arg = b.repr u 0 := by simpa [Complex.cos_arg hz, hzn, z]
    have hs : Real.sin z.arg = b.repr u 1 := by simpa [Complex.sin_arg, hzn, z]
    rw [circlePt, zero_add, one_smul, hc, hs]
    have h := b.sum_repr u
    simpa [Fin.sum_univ_succ, hb0, hb1, hb2, hpcoord] using h

private theorem W3CapReuse12_frameTriple (D : Pt) (hoff : offAxis D) :
    Orthonormal ℝ ![EA D 0, EA D 1, nAv D] := by
  rcases W3CapReuse12_axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  have hf : ‖unitDir (rawA D)‖ = 1 := by
    simp [unitDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (rawA D)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]
  have hnf : inner ℝ (nAv D) (unitDir (rawA D)) = 0 := by
    rw [unitDir, real_inner_smul_right, ho, mul_zero]
  have hc : ‖cross (nAv D) (unitDir (rawA D))‖ ^ 2 = 1 := by
    rw [W3CapReuse12_cross_norm_sq_native, hn, hf, hnf]
    norm_num
  have hf0 : inner ℝ (unitDir (rawA D)) (cross (nAv D) (unitDir (rawA D))) = 0 :=
    W3CapReuse12_cross_inner_second _ _
  have hn0 : inner ℝ (nAv D) (cross (nAv D) (unitDir (rawA D))) = 0 :=
    W3CapReuse12_cross_inner_first _ _
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [EA, real_inner_self_eq_norm_sq, hf, hn, hc, hf0, hn0, hnf, real_inner_comm]

private theorem W3CapReuse12_movingA_radius (D : Pt) (hL : D ∈ LamC) :
    0 < rA D ∧ (rA D)^2 = 1-‖D‖^2/4 := by
  have hnorm : ‖D‖ ≤ 1 := by
    simpa [LamC, Metric.mem_closedBall] using hL.1
  have hn0 := norm_nonneg D
  have hp : 0 < 1-‖D‖^2/4 := by nlinarith
  exact ⟨by simpa [rA] using Real.sqrt_pos.2 hp,
    by simpa [rA] using Real.sq_sqrt hp.le⟩

private theorem W3CapReuse12_movingA_full (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.u D '' Set.Icc (-Real.pi) Real.pi =
      {x : Pt | ‖x‖=1 ∧ ‖D+x‖=1} := by
  rcases W3CapReuse12_axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  rcases W3CapReuse12_movingA_radius D hL with ⟨hrr, hrr2⟩
  have himg := W3CapReuse12_fullCircleImage (EA D 0) (EA D 1) (nAv D) (W3CapReuse12_frameTriple D hoff)
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    let y : Pt := circlePt 0 (EA D 0) (EA D 1) 1 t
    have hy : y ∈ greatCircle (nAv D) := by
      rw [← himg]
      exact ⟨t, ht, rfl⟩
    have hysq : ‖y‖^2=1 := by rw [hy.1]; norm_num
    have hDy : inner ℝ D y = 0 := by
      have h := hy.2
      rw [nAv, real_inner_smul_left, inner_neg_left] at h
      have hne : ‖D‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hD)
      exact (neg_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hne))
    have hchart : HardSphereB5.SphericalCrofton.Aux.MovingArc.u D t = HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D + rA D • y := by
      simp [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, circlePt, y]
    rw [hchart]
    have hsum : D+(HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D+rA D•y) = (1/2 : ℝ)•D+rA D•y := by
      simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.cA]
      module
    constructor
    · have hsq : ‖HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D+rA D•y‖^2=1 := by
        rw [norm_add_sq_real]
        simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, norm_smul, Real.norm_eq_abs, real_inner_smul_left,
          real_inner_smul_right, hDy]
        norm_num [abs_of_pos hrr]
        nlinarith [hrr2]
      nlinarith [norm_nonneg (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D+rA D•y)]
    · rw [hsum]
      have hsq : ‖(1/2:ℝ)•D+rA D•y‖^2=1 := by
        rw [norm_add_sq_real]
        simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left,
          real_inner_smul_right, hDy]
        norm_num [abs_of_pos hrr]
        nlinarith [hrr2]
      nlinarith [norm_nonneg ((1/2:ℝ)•D+rA D•y)]
  · rintro ⟨hx, hDx⟩
    have hDxsq := norm_add_sq_real D x
    rw [hx, hDx] at hDxsq
    have hinner : inner ℝ D x = -(‖D‖^2)/2 := by nlinarith
    let y : Pt := (rA D)⁻¹ • (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)
    have hDy : inner ℝ D (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) = 0 := by
      rw [inner_sub_right, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right, real_inner_self_eq_norm_sq, hinner]
      ring
    have hyperp : inner ℝ (nAv D) y = 0 := by
      change inner ℝ (‖D‖⁻¹ • (-D)) ((rA D)⁻¹ • (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)) = 0
      rw [real_inner_smul_left, real_inner_smul_right, inner_neg_left, hDy]
      ring
    have hxcsq : ‖x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D‖^2 = (rA D)^2 := by
      rw [norm_sub_sq_real, hx, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right,
        ← real_inner_comm x D, hinner, norm_smul]
      norm_num
      nlinarith [hrr2]
    have hxc : ‖x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D‖=rA D := by
      nlinarith [norm_nonneg (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)]
    have hynorm : ‖y‖=1 := by
      change ‖(rA D)⁻¹ • (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrr, hxc,
        inv_mul_cancel₀ hrr.ne']
    have hy : y ∈ greatCircle (nAv D) := ⟨hynorm, hyperp⟩
    rw [← himg] at hy
    rcases hy with ⟨t, ht, hty⟩
    refine ⟨t, ht, ?_⟩
    have hchart : HardSphereB5.SphericalCrofton.Aux.MovingArc.u D t = HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D + rA D •
        (circlePt 0 (EA D 0) (EA D 1) 1 t) := by
      simp [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, circlePt]
    rw [hchart, hty]
    simp [y, smul_smul, mul_inv_cancel₀ hrr.ne']

private theorem W3CapReuse12_cutBoundsProof (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D)
    (hRc : Rc ‖D‖ ‖D - e‖ < 1) : 0 < cutA D ∧ cutA D < 1 := by
  let a : ℝ := ‖D‖
  let b : ℝ := ‖D - e‖
  let t : ℝ := inner ℝ D e
  let K : ℝ := a ^ 2 - t ^ 2
  let H : ℝ := (a + b + 1) * (a + b - 1) * (a - b + 1) * (-a + b + 1)
  have he : ‖e‖ = (1 : ℝ) := by simp [e]
  have hD : D ≠ 0 := by simpa using (hoff 0)
  have hDe : D - e ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa using (hoff 1)
  have ha : 0 < a := norm_pos_iff.mpr hD
  have hb : 0 < b := norm_pos_iff.mpr hDe
  have hnorms : a ≤ 1 ∧ b ≤ 1 := by
    simpa [LamC, Metric.mem_closedBall, dist_eq_norm, a, b] using hL
  have ha2 : a ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ ha.le (by norm_num : (0 : ℝ) ≤ 1)).2 hnorms.1
  have hb_sq : b ^ 2 = a ^ 2 - 2 * t + 1 := by
    have hh := norm_sub_sq_real D e
    rw [he] at hh
    simpa only [one_pow] using hh
  have ht : t < 1 := by
    have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
    nlinarith only [hb_sq, ha2, hb2]
  have hproj : ‖D - t • e‖ ^ 2 = K := by
    have hi : inner ℝ D (t • e) = t ^ 2 := by
      rw [inner_smul_right]
      change t * t = t ^ 2
      ring
    have hn : ‖t • e‖ ^ 2 = t ^ 2 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
    have hh := norm_sub_sq_real D (t • e)
    rw [hi, hn] at hh
    change ‖D - t • e‖ ^ 2 = a ^ 2 - 2 * t ^ 2 + t ^ 2 at hh
    dsimp [K]
    nlinarith only [hh]
  have hK : 0 < K := by
    rw [← hproj]
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hoff t)))
  have hH : H = 4 * K := by
    calc
      H = 4 * a ^ 2 - (a ^ 2 + 1 - b ^ 2) ^ 2 := by dsimp [H]; ring
      _ = 4 * K := by rw [hb_sq]; dsimp [K]; ring
  have hHpos : 0 < H := by rw [hH]; positivity
  have hRC : a * b < Real.sqrt H := by
    change a * b / Real.sqrt H < 1 at hRc
    have hh := (div_lt_iff₀ (Real.sqrt_pos.2 hHpos)).mp hRc
    simpa only [one_mul] using hh
  have hRCsq : a ^ 2 * b ^ 2 < 4 * K := by
    have hh := (sq_lt_sq₀ (mul_pos ha hb).le (Real.sqrt_nonneg H)).2 hRC
    rw [mul_pow, Real.sq_sqrt hHpos.le, hH] at hh
    exact hh
  let n : Pt := nAv D
  let s : ℝ := inner ℝ n e
  have hnn : ‖n‖ = 1 := by
    dsimp [n, nAv]
    rw [norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
    exact inv_mul_cancel₀ ha.ne'
  have hs : s = -(t / a) := by
    dsimp [s, n, nAv]
    rw [inner_smul_left, inner_neg_left]
    change a⁻¹ * -t = -(t / a)
    ring
  have hraw_def : rawA D = e - s • n := rfl
  have hrawnorm : ‖rawA D‖ ^ 2 = 1 - s ^ 2 := by
    have hi : inner ℝ e (s • n) = s ^ 2 := by
      rw [inner_smul_right, real_inner_comm n e]
      change s * s = s ^ 2
      ring
    have hn : ‖s • n‖ ^ 2 = s ^ 2 := by
      rw [norm_smul, hnn, mul_one, Real.norm_eq_abs, sq_abs]
    have hh := norm_sub_sq_real e (s • n)
    rw [← hraw_def, he, hi, hn] at hh
    nlinarith only [hh]
  have hrawsq : a ^ 2 * ‖rawA D‖ ^ 2 = K := by
    rw [hrawnorm, hs]
    dsimp [K]
    field_simp [ha.ne']
    <;> ring
  have hrawpos : 0 < ‖rawA D‖ := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro hh
    have hz : ‖rawA D‖ = 0 := hh.symm
    rw [hz] at hrawsq
    norm_num at hrawsq
    linarith only [hrawsq, hK]
  have hrarg : 0 < 1 - a ^ 2 / 4 := by linarith only [ha2]
  have hr : 0 < rA D := Real.sqrt_pos.2 hrarg
  have hrsq : rA D ^ 2 = 1 - a ^ 2 / 4 := Real.sq_sqrt hrarg.le
  let den : ℝ := 2 * rA D * ‖rawA D‖
  have hden : 0 < den := by dsimp [den]; positivity
  have hdensq : a ^ 2 * den ^ 2 = (4 - a ^ 2) * K := by
    calc
      a ^ 2 * den ^ 2 = 4 * rA D ^ 2 * (a ^ 2 * ‖rawA D‖ ^ 2) := by dsimp [den]; ring
      _ = (4 - a ^ 2) * K := by rw [hrsq, hrawsq]; ring
  have hgap : a ^ 2 * (den ^ 2 - (1 - t) ^ 2) = 4 * K - a ^ 2 * b ^ 2 := by
    rw [mul_sub, hdensq, hb_sq]
    dsimp [K]
    ring
  have hprodpos : 0 < a ^ 2 * (den ^ 2 - (1 - t) ^ 2) := by
    rw [hgap]
    linarith only [hRCsq]
  have hg : (1 - t) ^ 2 < den ^ 2 := by
    by_contra hh
    have hh' : den ^ 2 - (1 - t) ^ 2 ≤ 0 := by linarith only [le_of_not_gt hh]
    have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hh'
    linarith only [hm, hprodpos]
  have hnum : 0 < 1 - t := sub_pos.mpr ht
  have hlt : 1 - t < den := (sq_lt_sq₀ hnum.le hden.le).mp hg
  change 0 < (1 - t) / den ∧ (1 - t) / den < 1
  exact ⟨div_pos hnum hden, (div_lt_iff₀ hden).mpr (by simpa using hlt)⟩

private theorem W3CapReuse12_endpointBoundaryA (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D)
    (t : ℝ) (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    dist (D + u D t) e = 1 ↔ Real.cos t = cutA D := by
  rcases W3CapReuse12_axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  have hf := W3CapReuse12_frameProof D hoff
  have hrr := (W3CapReuse12_movingA_radius D hL).1
  have hrn : 0 < ‖rawA D‖ := norm_pos_iff.mpr hr
  have hu : ‖u D t‖ = 1 ∧ ‖D + u D t‖ = 1 := by
    have hmem : u D t ∈ u D '' Set.Icc (-Real.pi) Real.pi := ⟨t, ht, rfl⟩
    rw [W3CapReuse12_movingA_full D hL hoff] at hmem
    exact hmem
  have hinner : inner ℝ D (u D t) = -(‖D‖ ^ 2) / 2 := by
    have hs := norm_add_sq_real D (u D t)
    rw [hu.1, hu.2] at hs
    nlinarith only [hs]
  have hperp : inner ℝ (nAv D) (u D t - HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) = 0 := by
    simp only [nAv, inner_sub_right, real_inner_smul_left, inner_neg_left,
      HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right, real_inner_self_eq_norm_sq, hinner]
    ring
  have hproj : ‖rawA D‖ * inner ℝ (EA D 0) (u D t - HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) =
      inner ℝ e (u D t - HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) := by
    change ‖rawA D‖ * inner ℝ (‖rawA D‖⁻¹ • rawA D) _ = _
    rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hrn.ne', one_mul,
      rawA, inner_sub_left, real_inner_smul_left, hperp, mul_zero, sub_zero]
  have hcoord : inner ℝ (EA D 0) (u D t - HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) = rA D * Real.cos t := by
    simp [u, circlePt, inner_add_right, inner_smul_right,
      orthonormal_iff_ite.mp hf, hf.norm_eq_one]
  have hlin : ‖rawA D‖ * (rA D * Real.cos t) =
      inner ℝ (u D t) e + inner ℝ D e / 2 := by
    rw [← hcoord, hproj, inner_sub_right, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right,
      real_inner_comm (u D t) e, real_inner_comm D e]
    ring
  let den : ℝ := 2 * rA D * ‖rawA D‖
  have hden : 0 < den := by dsimp [den]; positivity
  have hlin2 : den * Real.cos t = 2 * inner ℝ (u D t) e + inner ℝ D e := by
    dsimp [den]
    nlinarith only [hlin]
  have hcut : den * cutA D = 1 - inner ℝ D e := by
    change den * ((1 - inner ℝ D e) / den) = _
    field_simp [hden.ne']
  have he : ‖(e : Pt)‖ = 1 := by simp [e]
  have hsq := norm_sub_sq_real (D + u D t) e
  rw [hu.2, he, inner_add_left] at hsq
  constructor
  · intro hd
    rw [dist_eq_norm] at hd
    rw [hd] at hsq
    have hscaled : den * Real.cos t = den * cutA D := by
      nlinarith only [hsq, hlin2, hcut]
    exact mul_left_cancel₀ hden.ne' hscaled
  · intro hc
    rw [hc] at hlin2
    have hxnorm : ‖D + u D t - e‖ = 1 := by
      nlinarith only [hsq, hlin2, hcut, norm_nonneg (D + u D t - e)]
    simpa only [dist_eq_norm] using hxnorm

private theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.endpointsA (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D)
    (hRc : Rc ‖D‖ ‖D - e‖ < 1) :
    vertsD D = {u D (-(halfA D)), u D (halfA D)} := by
  have hcut := W3CapReuse12_cutBoundsProof D hL hoff hRc
  have hh0 : 0 ≤ halfA D := Real.arccos_nonneg _
  have hhpi : halfA D ≤ Real.pi := Real.arccos_le_pi _
  have hcos : Real.cos (halfA D) = cutA D :=
    Real.cos_arccos (by linarith only [hcut.1]) hcut.2.le
  have htm : -(halfA D) ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨neg_le_neg hhpi, (neg_nonpos.mpr hh0).trans Real.pi_pos.le⟩
  have htp : halfA D ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(neg_nonpos.mpr Real.pi_pos.le).trans hh0, hhpi⟩
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hDx, hxe⟩
    have hfull : x ∈ u D '' Set.Icc (-Real.pi) Real.pi := by
      rw [W3CapReuse12_movingA_full D hL hoff]
      exact ⟨hx, hDx⟩
    rcases hfull with ⟨t, ht, htx⟩
    have hc : Real.cos t = cutA D := (W3CapReuse12_endpointBoundaryA D hL hoff t ht).mp (by
      rw [htx]
      exact hxe)
    have habs : |t| = halfA D :=
      Real.strictAntiOn_cos.injOn ⟨abs_nonneg t, abs_le.mpr ht⟩ ⟨hh0, hhpi⟩ (by
        rw [Real.cos_abs, hcos]
        exact hc)
    rcases le_total 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0] at habs
      right
      rw [← htx, habs]
    · rw [abs_of_nonpos ht0] at habs
      have hneg : t = -(halfA D) := by linarith only [habs]
      left
      rw [← htx, hneg]
  · rintro (rfl | rfl)
    · have hn : ‖u D (-(halfA D))‖ = 1 ∧ ‖D + u D (-(halfA D))‖ = 1 := by
        have hmem : u D (-(halfA D)) ∈ u D '' Set.Icc (-Real.pi) Real.pi :=
          ⟨-(halfA D), htm, rfl⟩
        rw [W3CapReuse12_movingA_full D hL hoff] at hmem
        exact hmem
      exact ⟨hn.1, hn.2, (W3CapReuse12_endpointBoundaryA D hL hoff _ htm).mpr (by
        rw [Real.cos_neg, hcos])⟩
    · have hn : ‖u D (halfA D)‖ = 1 ∧ ‖D + u D (halfA D)‖ = 1 := by
        have hmem : u D (halfA D) ∈ u D '' Set.Icc (-Real.pi) Real.pi :=
          ⟨halfA D, htp, rfl⟩
        rw [W3CapReuse12_movingA_full D hL hoff] at hmem
        exact hmem
      exact ⟨hn.1, hn.2, (W3CapReuse12_endpointBoundaryA D hL hoff _ htp).mpr hcos⟩
end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

private theorem HardSphereB5.SphericalCrofton.Aux.Cap.sigma_caps_data (D : Pt) (hD0 : D ≠ 0) (hDe : D ≠ e) :
    ‖nAv D‖ = 1 ∧ ‖nBv D‖ = 1 ∧
      SigmaD D = cap (nAv D) (‖D‖ / 2) ∩ cap (nBv D) (‖D - e‖ / 2) := by
  have hA : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  have hB : 0 < ‖D - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hDe)
  have hneg : ‖-D‖ = ‖D‖ := norm_neg D
  have hdiff : ‖e - D‖ = ‖D - e‖ := norm_sub_rev e D
  refine ⟨?_, ?_, ?_⟩
  · rw [nAv, norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hA), inv_mul_cancel₀ hA.ne']
  · rw [nBv, norm_smul, hdiff, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hB), inv_mul_cancel₀ hB.ne']
  · ext u
    have hiA : inner ℝ (nAv D) u = -(inner ℝ D u) / ‖D‖ := by
      simp only [nAv, real_inner_smul_left, inner_neg_left]
      ring
    have hiB : inner ℝ (nBv D) u = -(inner ℝ (D - e) u) / ‖D - e‖ := by
      simp only [nBv, real_inner_smul_left,
        show e - D = -(D - e) by abel, inner_neg_left]
      ring
    have hiff (a x : ℝ) (ha : 0 < a) : a ^ 2 + 2 * x ≤ 0 ↔ a / 2 ≤ -x / a := by
      rw [le_div_iff₀ ha]
      constructor <;> intro h <;> nlinarith
    simp only [SigmaD, LamC, Set.mem_setOf_eq, Set.mem_inter_iff,
      Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero]
    constructor
    · rintro ⟨hu, hballs⟩
      obtain ⟨ha, hb⟩ := (SphereGeom.Aux.TwoBalls.ball_iff_inner D e u hu).mp hballs
      exact ⟨⟨hu, by rw [hiA]; exact (hiff _ _ hA).mp ha⟩,
        ⟨hu, by rw [hiB]; exact (hiff _ _ hB).mp hb⟩⟩
    · rintro ⟨⟨hu, ha⟩, ⟨_, hb⟩⟩
      refine ⟨hu, (SphereGeom.Aux.TwoBalls.ball_iff_inner D e u hu).mpr ⟨?_, ?_⟩⟩
      · exact (hiff _ _ hA).mpr (by simpa only [hiA] using ha)
      · exact (hiff _ _ hB).mpr (by simpa only [hiB] using hb)

end

section

open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

private theorem HardSphereB5.SphericalCrofton.Aux.Cap.frontier_slice (n : Pt) (hn : ‖n‖ = 1) (h : ℝ) (h0 : 0 < h) (h1 : h < 1) :
    sFrontier (cap n h) = {u : Pt | ‖u‖ = 1 ∧ inner ℝ n u = h} := by
  let S := Metric.sphere (0 : Pt) 1
  let A : Set S := (Subtype.val : S → Pt) ⁻¹' cap n h
  have hu1 : ∀ u : S, ‖(u : Pt)‖ = 1 := by
    intro u
    simpa [Metric.mem_sphere, dist_zero_right] using u.property
  have hA : A = {u : S | h ≤ inner ℝ n (u : Pt)} := by
    ext u
    change (‖(u : Pt)‖ = 1 ∧ h ≤ inner ℝ n (u : Pt)) ↔ h ≤ inner ℝ n (u : Pt)
    simp [hu1 u]
  have hcA : IsClosed A := by
    rw [hA]
    exact isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  change Subtype.val '' frontier A = _
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hum : u ∈ A := by
      have hh := hu.1
      rwa [hcA.closure_eq] at hh
    have hul : h ≤ inner ℝ n (u : Pt) := by simpa only [hA, Set.mem_setOf_eq] using hum
    refine ⟨hu1 u, le_antisymm ?_ hul⟩
    by_contra hh
    have hs : h < inner ℝ n (u : Pt) := lt_of_not_ge hh
    have hopen : IsOpen {v : S | h < inner ℝ n (v : Pt)} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
    have hsub : {v : S | h < inner ℝ n (v : Pt)} ⊆ A := by
      rw [hA]
      intro v hv
      exact (show h < inner ℝ n (v : Pt) from hv).le
    have hin : u ∈ interior A := interior_mono hsub (by rw [hopen.interior_eq]; exact hs)
    exact hu.2 hin
  · rintro ⟨hx, hnx⟩
    let us : S := ⟨x, by simpa [S, Metric.mem_sphere, dist_zero_right] using hx⟩
    have hmemA : us ∈ A := by rw [hA]; change h ≤ inner ℝ n x; rw [hnx]
    refine ⟨us, ⟨subset_closure hmemA, ?_⟩, rfl⟩
    intro hinter
    have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
    have hxn : inner ℝ x n = h := by rw [real_inner_comm]; exact hnx
    let z : Pt := x - h • n
    have hnz : inner ℝ n z = 0 := by
      change inner ℝ n (x - h • n) = 0
      rw [inner_sub_right, real_inner_smul_right, hnx, hnn]
      ring
    have hzn : inner ℝ z n = 0 := by rw [real_inner_comm]; exact hnz
    have hzz : inner ℝ z z = 1 - h ^ 2 := by
      change inner ℝ (x - h • n) (x - h • n) = 1 - h ^ 2
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        hxx, hnx, hxn, hnn]
      ring
    have hs : 0 < 1 - h ^ 2 := by nlinarith
    let r : ℝ := Real.sqrt (1 - h ^ 2)
    have hr0 : 0 < r := Real.sqrt_pos.2 hs
    have hr2 : r ^ 2 = 1 - h ^ 2 := Real.sq_sqrt hs.le
    let q : Pt := r⁻¹ • z
    have hnq : inner ℝ n q = 0 := by simp [q, real_inner_smul_right, hnz]
    have hqn : inner ℝ q n = 0 := by rw [real_inner_comm]; exact hnq
    have hqq : inner ℝ q q = 1 := by
      change inner ℝ (r⁻¹ • z) (r⁻¹ • z) = 1
      simp only [real_inner_smul_left, real_inner_smul_right, hzz]
      rw [← hr2]
      field_simp
    let D := Set.Ioo (-1 : ℝ) 1
    have hpunit : ∀ t : D, ‖(t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q‖ = 1 := by
      intro t
      have ht0 : 0 ≤ 1 - (t : ℝ) ^ 2 := by nlinarith [t.property.1, t.property.2]
      have htsq := Real.sq_sqrt ht0
      have hh : ‖(t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
          hnn, hnq, hqn, hqq]
        nlinarith
      nlinarith [norm_nonneg ((t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q)]
    let f : D → S := fun t => ⟨(t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q,
      by simpa [S, Metric.mem_sphere, dist_zero_right] using hpunit t⟩
    have hfc : Continuous f := by dsimp [f]; continuity
    let th : D := ⟨h, ⟨by linarith, h1⟩⟩
    have hf0 : f th = us := by
      apply Subtype.ext
      change h • n + r • (r⁻¹ • (x - h • n)) = x
      rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
      abel
    have hpre : f ⁻¹' A = (Subtype.val : D → ℝ) ⁻¹' Set.Ici h := by
      ext t
      change (‖(t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q‖ = 1 ∧
        h ≤ inner ℝ n ((t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q)) ↔ h ≤ (t : ℝ)
      rw [hpunit t]
      simp only [inner_add_right, real_inner_smul_right, hnn, hnq, mul_one, mul_zero, add_zero, true_and]
    have ht : th ∈ interior (f ⁻¹' A) := preimage_interior_subset_interior_preimage hfc
      (show th ∈ f ⁻¹' interior A by rw [Set.mem_preimage, hf0]; exact hinter)
    rw [hpre] at ht
    have hreal : (th : ℝ) ∈ interior (Set.Ici h) :=
      IsOpenMap.interior_preimage_subset_preimage_interior
        ((isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1)).isOpenEmbedding_subtypeVal.isOpenMap) ht
    have hh : h < h := by simpa [th, interior_Ici] using hreal
    exact lt_irrefl h hh
end

section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 600000

private theorem HardSphereB5.SphericalCrofton.Aux.frontierSigma_subset_arcs (D : Pt) :
    sFrontier (SigmaD D) ⊆ arcA D ∪ arcB D := by
  let S := Metric.sphere (0 : Pt) 1
  let A : Set S := {y | ‖D + (y : Pt)‖ ≤ 1}
  let B : Set S := {y | dist (D + (y : Pt)) e ≤ 1}
  have hu (y : S) : ‖(y : Pt)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using y.property
  have hA : IsClosed A := isClosed_le (by fun_prop) continuous_const
  have hB : IsClosed B := isClosed_le (by fun_prop) continuous_const
  have hset : (Subtype.val : S → Pt) ⁻¹' SigmaD D = A ∩ B := by
    ext y
    simp [SigmaD, LamC, A, B, hu y, Metric.mem_closedBall, dist_zero_right]
  rintro u ⟨y,hy,rfl⟩
  change y ∈ frontier ((Subtype.val : S → Pt) ⁻¹' SigmaD D) at hy
  rw [hset] at hy
  have hyAB : y ∈ A ∩ B := (hA.inter hB).frontier_subset hy
  have hyS : (y : Pt) ∈ SigmaD D := by
    change y ∈ (Subtype.val : S → Pt) ⁻¹' SigmaD D
    rw [hset]
    exact hyAB
  rcases frontier_inter_subset A B hy with hyA | hyB
  · by_cases h0 : D = 0
    · have hAu : A = Set.univ := by ext z; simp [A, h0, hu z]
      have hfalse := hyA.1
      simp [hAu] at hfalse
    · apply Or.inl
      simp only [arcA, if_neg h0, Set.mem_setOf_eq]
      refine ⟨hyS, ?_⟩
      exact frontier_le_subset_eq (show Continuous (fun y : S => ‖D + (y : Pt)‖) by fun_prop)
        continuous_const hyA.1
  · by_cases he : D = e
    · have hBu : B = Set.univ := by
        ext z
        simp [B, he, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, hu z]
      have hfalse := hyB.2
      simp [hBu] at hfalse
    · apply Or.inr
      simp only [arcB, if_neg he, Set.mem_setOf_eq]
      refine ⟨hyS, ?_⟩
      exact frontier_le_subset_eq (show Continuous (fun y : S => dist (D + (y : Pt)) e) by fun_prop)
        continuous_const hyB.2
end

open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical
open Topology Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom
open HardSphereB5.SphericalCrofton.Aux.MovingArc

private theorem cross_norm_sq_native (a b : Pt) :
    ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - inner ℝ a b ^ 2 := by
  simp [SphereGeom.cross, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
    cross_apply, Fin.sum_univ_succ]
  ring

private theorem cross_inner_first (a b : Pt) : inner ℝ a (cross a b) = 0 := by
  simp [SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
  ring

private theorem cross_inner_second (a b : Pt) : inner ℝ b (cross a b) = 0 := by
  simp [SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
  ring

private theorem axisA_facts (D : Pt) (hoff : offAxis D) :
    D ≠ 0 ∧ ‖nAv D‖ = 1 ∧ rawA D ≠ 0 ∧
      inner ℝ (nAv D) (rawA D) = 0 := by
  have hD : D ≠ 0 := by
    intro hd
    exact hoff 0 (by simpa using hd)
  have hn : ‖nAv D‖ = 1 := by
    simp [nAv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg D),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hD)]
  have horth : inner ℝ (nAv D) (rawA D) = 0 := by
    simp only [rawA, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  have he : ‖(e : Pt)‖ = 1 := by simp [e]
  have hraw : rawA D ≠ 0 := by
    intro hr
    have heq : e = (inner ℝ (nAv D) e) • nAv D := sub_eq_zero.mp hr
    have hcoeff : inner ℝ (nAv D) e ≠ 0 := by
      intro hc
      rw [hc, zero_smul] at heq
      have hbad := congrArg norm heq
      rw [he, norm_zero] at hbad
      norm_num at hbad
    have hDaxis : D = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) • e := by
      calc
        D = (-‖D‖) • nAv D := by
          simp [nAv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hD)]
        _ = ((-‖D‖ * (inner ℝ (nAv D) e)⁻¹) * inner ℝ (nAv D) e) • nAv D := by
          rw [mul_assoc, inv_mul_cancel₀ hcoeff, mul_one]
        _ = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) •
            ((inner ℝ (nAv D) e) • nAv D) := by rw [smul_smul]
        _ = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) • e := by rw [← heq]
    exact hoff _ hDaxis
  exact ⟨hD, hn, hraw, horth⟩

private theorem frameProof (D : Pt) (hoff : offAxis D) : Orthonormal ℝ (EA D) := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  have hf : ‖unitDir (rawA D)‖ = 1 := by
    simp [unitDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (rawA D)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]
  have hnf : inner ℝ (nAv D) (unitDir (rawA D)) = 0 := by
    rw [unitDir, real_inner_smul_right, ho, mul_zero]
  have hc : ‖cross (nAv D) (unitDir (rawA D))‖ ^ 2 = 1 := by
    rw [cross_norm_sq_native, hn, hf, hnf]
    norm_num
  have hf0 : inner ℝ (unitDir (rawA D)) (cross (nAv D) (unitDir (rawA D))) = 0 :=
    cross_inner_second _ _
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [EA, real_inner_self_eq_norm_sq, hf, hc, hf0, real_inner_comm]

private theorem fullCircleImage (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁, v₂, p]) :
    circlePt 0 v₁ v₂ 1 '' Set.Icc (-Real.pi) Real.pi = greatCircle p := by
  let e : Fin 3 → E3 := ![v₁, v₂, p]
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range e) := by
    apply Eq.ge
    apply hv.linearIndependent.span_eq_top_of_card_eq_finrank
    simp [E3]
  let b : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk hv hspan
  have hb (i : Fin 3) : b i = e i := by simp [b, e]
  have hb0 : b 0 = v₁ := by simp [hb, e]
  have hb1 : b 1 = v₂ := by simp [hb, e]
  have hb2 : b 2 = p := by simp [hb, e]
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · have hc : circlePt 0 v₁ v₂ 1 t = b.repr.symm (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0]) := by
        rw [← b.sum_repr_symm]
        simp [Fin.sum_univ_succ, hb0, hb1, hb2, circlePt]
      rw [hc, b.repr.symm.norm_map]
      have hs : ‖(WithLp.toLp 2 ![Real.cos t, Real.sin t, 0] : E3)‖ ^ 2 = 1 := by
        simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Real.cos_sq_add_sin_sq]
      nlinarith [norm_nonneg (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0] : E3)]
    · have h1 : inner ℝ p v₁ = 0 := by simpa [e] using hv.inner_eq_zero (show (2 : Fin 3) ≠ 0 by decide)
      have h2 : inner ℝ p v₂ = 0 := by simpa [e] using hv.inner_eq_zero (show (2 : Fin 3) ≠ 1 by decide)
      simp [circlePt, inner_add_right, inner_smul_right, h1, h2]
  · rintro ⟨hu, hup⟩
    have hpcoord : b.repr u 2 = 0 := by simpa [b.repr_apply_apply, hb2] using hup
    have hnorm : b.repr u 0 ^ 2 + b.repr u 1 ^ 2 = 1 := by
      have h : ‖b.repr u‖ ^ 2 = 1 := by rw [b.repr.norm_map, hu]; norm_num
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simpa [Fin.sum_univ_succ, hpcoord] using h
    let z : ℂ := ⟨b.repr u 0, b.repr u 1⟩
    have hzn : ‖z‖ = 1 := by
      have h : ‖z‖ ^ 2 = 1 := by
        rw [Complex.sq_norm]
        simpa [Complex.normSq, z, pow_two] using hnorm
      nlinarith [norm_nonneg z]
    have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; norm_num at hzn
    refine ⟨z.arg, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
    have hc : Real.cos z.arg = b.repr u 0 := by simpa [Complex.cos_arg hz, hzn, z]
    have hs : Real.sin z.arg = b.repr u 1 := by simpa [Complex.sin_arg, hzn, z]
    rw [circlePt, zero_add, one_smul, hc, hs]
    have h := b.sum_repr u
    simpa [Fin.sum_univ_succ, hb0, hb1, hb2, hpcoord] using h

private theorem frameTriple (D : Pt) (hoff : offAxis D) :
    Orthonormal ℝ ![EA D 0, EA D 1, nAv D] := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  have hf : ‖unitDir (rawA D)‖ = 1 := by
    simp [unitDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (rawA D)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]
  have hnf : inner ℝ (nAv D) (unitDir (rawA D)) = 0 := by
    rw [unitDir, real_inner_smul_right, ho, mul_zero]
  have hc : ‖cross (nAv D) (unitDir (rawA D))‖ ^ 2 = 1 := by
    rw [cross_norm_sq_native, hn, hf, hnf]
    norm_num
  have hf0 : inner ℝ (unitDir (rawA D)) (cross (nAv D) (unitDir (rawA D))) = 0 :=
    cross_inner_second _ _
  have hn0 : inner ℝ (nAv D) (cross (nAv D) (unitDir (rawA D))) = 0 :=
    cross_inner_first _ _
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [EA, real_inner_self_eq_norm_sq, hf, hn, hc, hf0, hn0, hnf, real_inner_comm]

private theorem movingA_radius (D : Pt) (hL : D ∈ LamC) :
    0 < rA D ∧ (rA D)^2 = 1-‖D‖^2/4 := by
  have hnorm : ‖D‖ ≤ 1 := by
    simpa [LamC, Metric.mem_closedBall] using hL.1
  have hn0 := norm_nonneg D
  have hp : 0 < 1-‖D‖^2/4 := by nlinarith
  exact ⟨by simpa [rA] using Real.sqrt_pos.2 hp,
    by simpa [rA] using Real.sq_sqrt hp.le⟩

private theorem movingA_full (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.u D '' Set.Icc (-Real.pi) Real.pi =
      {x : Pt | ‖x‖=1 ∧ ‖D+x‖=1} := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  rcases movingA_radius D hL with ⟨hrr, hrr2⟩
  have himg := fullCircleImage (EA D 0) (EA D 1) (nAv D) (frameTriple D hoff)
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    let y : Pt := circlePt 0 (EA D 0) (EA D 1) 1 t
    have hy : y ∈ greatCircle (nAv D) := by
      rw [← himg]
      exact ⟨t, ht, rfl⟩
    have hysq : ‖y‖^2=1 := by rw [hy.1]; norm_num
    have hDy : inner ℝ D y = 0 := by
      have h := hy.2
      rw [nAv, real_inner_smul_left, inner_neg_left] at h
      have hne : ‖D‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hD)
      exact (neg_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hne))
    have hchart : HardSphereB5.SphericalCrofton.Aux.MovingArc.u D t = HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D + rA D • y := by
      simp [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, circlePt, y]
    rw [hchart]
    have hsum : D+(HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D+rA D•y) = (1/2 : ℝ)•D+rA D•y := by
      simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.cA]
      module
    constructor
    · have hsq : ‖HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D+rA D•y‖^2=1 := by
        rw [norm_add_sq_real]
        simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, norm_smul, Real.norm_eq_abs, real_inner_smul_left,
          real_inner_smul_right, hDy]
        norm_num [abs_of_pos hrr]
        nlinarith [hrr2]
      nlinarith [norm_nonneg (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D+rA D•y)]
    · rw [hsum]
      have hsq : ‖(1/2:ℝ)•D+rA D•y‖^2=1 := by
        rw [norm_add_sq_real]
        simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left,
          real_inner_smul_right, hDy]
        norm_num [abs_of_pos hrr]
        nlinarith [hrr2]
      nlinarith [norm_nonneg ((1/2:ℝ)•D+rA D•y)]
  · rintro ⟨hx, hDx⟩
    have hDxsq := norm_add_sq_real D x
    rw [hx, hDx] at hDxsq
    have hinner : inner ℝ D x = -(‖D‖^2)/2 := by nlinarith
    let y : Pt := (rA D)⁻¹ • (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)
    have hDy : inner ℝ D (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) = 0 := by
      rw [inner_sub_right, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right, real_inner_self_eq_norm_sq, hinner]
      ring
    have hyperp : inner ℝ (nAv D) y = 0 := by
      change inner ℝ (‖D‖⁻¹ • (-D)) ((rA D)⁻¹ • (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)) = 0
      rw [real_inner_smul_left, real_inner_smul_right, inner_neg_left, hDy]
      ring
    have hxcsq : ‖x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D‖^2 = (rA D)^2 := by
      rw [norm_sub_sq_real, hx, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right,
        ← real_inner_comm x D, hinner, norm_smul]
      norm_num
      nlinarith [hrr2]
    have hxc : ‖x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D‖=rA D := by
      nlinarith [norm_nonneg (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)]
    have hynorm : ‖y‖=1 := by
      change ‖(rA D)⁻¹ • (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrr, hxc,
        inv_mul_cancel₀ hrr.ne']
    have hy : y ∈ greatCircle (nAv D) := ⟨hynorm, hyperp⟩
    rw [← himg] at hy
    rcases hy with ⟨t, ht, hty⟩
    refine ⟨t, ht, ?_⟩
    have hchart : HardSphereB5.SphericalCrofton.Aux.MovingArc.u D t = HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D + rA D •
        (circlePt 0 (EA D 0) (EA D 1) 1 t) := by
      simp [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, circlePt]
    rw [hchart, hty]
    simp [y, smul_smul, mul_inv_cancel₀ hrr.ne']

private theorem cutBoundsProof (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D)
    (hRc : Rc ‖D‖ ‖D - e‖ < 1) : 0 < cutA D ∧ cutA D < 1 := by
  let a : ℝ := ‖D‖
  let b : ℝ := ‖D - e‖
  let t : ℝ := inner ℝ D e
  let K : ℝ := a ^ 2 - t ^ 2
  let H : ℝ := (a + b + 1) * (a + b - 1) * (a - b + 1) * (-a + b + 1)
  have he : ‖e‖ = (1 : ℝ) := by simp [e]
  have hD : D ≠ 0 := by simpa using (hoff 0)
  have hDe : D - e ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa using (hoff 1)
  have ha : 0 < a := norm_pos_iff.mpr hD
  have hb : 0 < b := norm_pos_iff.mpr hDe
  have hnorms : a ≤ 1 ∧ b ≤ 1 := by
    simpa [LamC, Metric.mem_closedBall, dist_eq_norm, a, b] using hL
  have ha2 : a ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ ha.le (by norm_num : (0 : ℝ) ≤ 1)).2 hnorms.1
  have hb_sq : b ^ 2 = a ^ 2 - 2 * t + 1 := by
    have hh := norm_sub_sq_real D e
    rw [he] at hh
    simpa only [one_pow] using hh
  have ht : t < 1 := by
    have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
    nlinarith only [hb_sq, ha2, hb2]
  have hproj : ‖D - t • e‖ ^ 2 = K := by
    have hi : inner ℝ D (t • e) = t ^ 2 := by
      rw [inner_smul_right]
      change t * t = t ^ 2
      ring
    have hn : ‖t • e‖ ^ 2 = t ^ 2 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
    have hh := norm_sub_sq_real D (t • e)
    rw [hi, hn] at hh
    change ‖D - t • e‖ ^ 2 = a ^ 2 - 2 * t ^ 2 + t ^ 2 at hh
    dsimp [K]
    nlinarith only [hh]
  have hK : 0 < K := by
    rw [← hproj]
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hoff t)))
  have hH : H = 4 * K := by
    calc
      H = 4 * a ^ 2 - (a ^ 2 + 1 - b ^ 2) ^ 2 := by dsimp [H]; ring
      _ = 4 * K := by rw [hb_sq]; dsimp [K]; ring
  have hHpos : 0 < H := by rw [hH]; positivity
  have hRC : a * b < Real.sqrt H := by
    change a * b / Real.sqrt H < 1 at hRc
    have hh := (div_lt_iff₀ (Real.sqrt_pos.2 hHpos)).mp hRc
    simpa only [one_mul] using hh
  have hRCsq : a ^ 2 * b ^ 2 < 4 * K := by
    have hh := (sq_lt_sq₀ (mul_pos ha hb).le (Real.sqrt_nonneg H)).2 hRC
    rw [mul_pow, Real.sq_sqrt hHpos.le, hH] at hh
    exact hh
  let n : Pt := nAv D
  let s : ℝ := inner ℝ n e
  have hnn : ‖n‖ = 1 := by
    dsimp [n, nAv]
    rw [norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
    exact inv_mul_cancel₀ ha.ne'
  have hs : s = -(t / a) := by
    dsimp [s, n, nAv]
    rw [inner_smul_left, inner_neg_left]
    change a⁻¹ * -t = -(t / a)
    ring
  have hraw_def : rawA D = e - s • n := rfl
  have hrawnorm : ‖rawA D‖ ^ 2 = 1 - s ^ 2 := by
    have hi : inner ℝ e (s • n) = s ^ 2 := by
      rw [inner_smul_right, real_inner_comm n e]
      change s * s = s ^ 2
      ring
    have hn : ‖s • n‖ ^ 2 = s ^ 2 := by
      rw [norm_smul, hnn, mul_one, Real.norm_eq_abs, sq_abs]
    have hh := norm_sub_sq_real e (s • n)
    rw [← hraw_def, he, hi, hn] at hh
    nlinarith only [hh]
  have hrawsq : a ^ 2 * ‖rawA D‖ ^ 2 = K := by
    rw [hrawnorm, hs]
    dsimp [K]
    field_simp [ha.ne']
    <;> ring
  have hrawpos : 0 < ‖rawA D‖ := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro hh
    have hz : ‖rawA D‖ = 0 := hh.symm
    rw [hz] at hrawsq
    norm_num at hrawsq
    linarith only [hrawsq, hK]
  have hrarg : 0 < 1 - a ^ 2 / 4 := by linarith only [ha2]
  have hr : 0 < rA D := Real.sqrt_pos.2 hrarg
  have hrsq : rA D ^ 2 = 1 - a ^ 2 / 4 := Real.sq_sqrt hrarg.le
  let den : ℝ := 2 * rA D * ‖rawA D‖
  have hden : 0 < den := by dsimp [den]; positivity
  have hdensq : a ^ 2 * den ^ 2 = (4 - a ^ 2) * K := by
    calc
      a ^ 2 * den ^ 2 = 4 * rA D ^ 2 * (a ^ 2 * ‖rawA D‖ ^ 2) := by dsimp [den]; ring
      _ = (4 - a ^ 2) * K := by rw [hrsq, hrawsq]; ring
  have hgap : a ^ 2 * (den ^ 2 - (1 - t) ^ 2) = 4 * K - a ^ 2 * b ^ 2 := by
    rw [mul_sub, hdensq, hb_sq]
    dsimp [K]
    ring
  have hprodpos : 0 < a ^ 2 * (den ^ 2 - (1 - t) ^ 2) := by
    rw [hgap]
    linarith only [hRCsq]
  have hg : (1 - t) ^ 2 < den ^ 2 := by
    by_contra hh
    have hh' : den ^ 2 - (1 - t) ^ 2 ≤ 0 := by linarith only [le_of_not_gt hh]
    have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hh'
    linarith only [hm, hprodpos]
  have hnum : 0 < 1 - t := sub_pos.mpr ht
  have hlt : 1 - t < den := (sq_lt_sq₀ hnum.le hden.le).mp hg
  change 0 < (1 - t) / den ∧ (1 - t) / den < 1
  exact ⟨div_pos hnum hden, (div_lt_iff₀ hden).mpr (by simpa using hlt)⟩

private theorem circleBandProof (c : E3) (E : Fin 2 → E3) (he : Orthonormal ℝ E)
    (r : ℝ) (hr : 0 < r) (k : ℝ) (hklo : -1 ≤ k) (hkhi : k ≤ 1) :
    circlePt c (E 0) (E 1) r '' Set.Icc (-Real.arccos k) (Real.arccos k) =
      {x | x ∈ circlePt c (E 0) (E 1) r '' Set.Icc (-Real.pi) Real.pi ∧
        r * k ≤ inner ℝ (E 0) (x - c)} := by
  have hcoord (t : ℝ) :
      inner ℝ (E 0) (circlePt c (E 0) (E 1) r t - c) = r * Real.cos t := by
    simp [circlePt, inner_add_right, inner_smul_right, orthonormal_iff_ite.mp he, he.norm_eq_one]
  have htrig (t : ℝ) (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
      k ≤ Real.cos t ↔ t ∈ Set.Icc (-Real.arccos k) (Real.arccos k) := by
    have ht_abs : |t| ≤ Real.pi := abs_le.mpr ht
    have hm : Real.cos (Real.arccos k) ≤ Real.cos |t| ↔ |t| ≤ Real.arccos k :=
      Real.strictAntiOn_cos.le_iff_ge
        ⟨Real.arccos_nonneg k, Real.arccos_le_pi k⟩ ⟨abs_nonneg t, ht_abs⟩
    simpa only [Real.cos_arccos hklo hkhi, Real.cos_abs, abs_le, Set.mem_Icc] using hm
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hfull : t ∈ Set.Icc (-Real.pi) Real.pi :=
      ⟨by linarith [ht.1, Real.arccos_le_pi k], by linarith [ht.2, Real.arccos_le_pi k]⟩
    refine ⟨⟨t, hfull, rfl⟩, ?_⟩
    rw [hcoord]
    exact mul_le_mul_of_nonneg_left ((htrig t hfull).mpr ht) hr.le
  · rintro ⟨⟨t, ht, rfl⟩, hcut⟩
    rw [hcoord] at hcut
    exact ⟨t, (htrig t ht).mp (le_of_mul_le_mul_left hcut hr), rfl⟩

private theorem arcAProof (D : Pt)
  (hL : D ∈ LamC) (hoff : offAxis D) (hRc : Rc ‖D‖ ‖D-e‖ < 1) :
  arcA D = HardSphereB5.SphericalCrofton.Aux.MovingArc.u D '' Set.Icc (-(halfA D)) (halfA D) := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  rcases movingA_radius D hL with ⟨hrr, hrr2⟩
  rcases cutBoundsProof D hL hoff hRc with ⟨hcut0, hcut1⟩
  have hrn : 0 < ‖rawA D‖ := norm_pos_iff.mpr hr
  have hrn2 : 0 < 2*‖rawA D‖ := by positivity
  have hcutR : rA D * cutA D = (1-inner ℝ D e)/(2*‖rawA D‖) := by
    rw [cutA]
    field_simp [hrr.ne', hrn.ne'] <;> ring
  have hchar (x : Pt) (hx : ‖x‖=1) (hDx : ‖D+x‖=1) :
      ‖D+x-e‖≤1 ↔ rA D * cutA D ≤
        inner ℝ (EA D 0) (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) := by
    have hDxsq := norm_add_sq_real D x
    rw [hx, hDx] at hDxsq
    have hinner : inner ℝ D x = -(‖D‖^2)/2 := by nlinarith
    have hperp : inner ℝ (nAv D) (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)=0 := by
      simp only [nAv, inner_sub_right, real_inner_smul_left, inner_neg_left,
        HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hinner]
      ring
    have hproj : ‖rawA D‖ * inner ℝ (EA D 0)
        (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) =
          inner ℝ e (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) := by
      change ‖rawA D‖ * inner ℝ (‖rawA D‖⁻¹ • rawA D) _ = _
      rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hrn.ne', one_mul,
        rawA, inner_sub_left, real_inner_smul_left, hperp, mul_zero, sub_zero]
    have hlin : ‖rawA D‖ * inner ℝ (EA D 0)
        (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) = inner ℝ x e + inner ℝ D e/2 := by
      rw [hproj, inner_sub_right, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right,
        real_inner_comm x e, real_inner_comm D e]
      ring
    have hesq : ‖(e : Pt)‖=1 := by simp [e]
    have hnorm := norm_sub_sq_real (D+x) e
    rw [hDx, hesq, inner_add_left] at hnorm
    rw [hcutR, div_le_iff₀ hrn2]
    constructor
    · intro hb
      have hb2 : ‖D+x-e‖^2≤1 := by nlinarith [norm_nonneg (D+x-e)]
      nlinarith
    · intro hb
      nlinarith [norm_nonneg (D+x-e)]
  change arcA D = circlePt (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) (EA D 0) (EA D 1) (rA D) ''
    Set.Icc (-Real.arccos (cutA D)) (Real.arccos (cutA D))
  rw [circleBandProof _ _ (frameProof D hoff) _ hrr _ (by linarith) hcut1.le]
  change arcA D = {x | x ∈ HardSphereB5.SphericalCrofton.Aux.MovingArc.u D '' Set.Icc (-Real.pi) Real.pi ∧ _}
  rw [movingA_full D hL hoff]
  ext x
  rw [arcA, if_neg hD]
  change (‖x‖=1 ∧ D+x∈LamC) ∧ ‖D+x‖=1 ↔
    (‖x‖=1 ∧ ‖D+x‖=1) ∧ rA D*cutA D ≤ inner ℝ (EA D 0)
      (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)
  constructor
  · rintro ⟨⟨hx,hLx⟩,hDx⟩
    refine ⟨⟨hx,hDx⟩,(hchar x hx hDx).1 ?_⟩
    simpa [LamC, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hLx.2
  · rintro ⟨⟨hx,hDx⟩,hband⟩
    refine ⟨⟨hx,?_,?_⟩,hDx⟩
    · simpa [Metric.mem_closedBall] using hDx.le
    · simpa [Metric.mem_closedBall, dist_eq_norm] using (hchar x hx hDx).2 hband

private theorem cross_add_native (a b c : Pt) : cross a (b+c) = cross a b + cross a c := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring

private theorem cross_smul_native (a b : Pt) (r : ℝ) : cross a (r•b) = r•cross a b := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring

private theorem cross_neg_native (a b : Pt) : cross (-a) (-b) = cross a b := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring

private theorem cross_cross_native (a b : Pt) :
    cross a (cross a b) = (inner ℝ a b)•a - ‖a‖^2•b := by
  ext i; fin_cases i <;>
    simp [SphereGeom.cross, cross_apply, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
      Fin.sum_univ_succ] <;> ring

private theorem cross_center_A (D : Pt) :
    cross (nAv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) = 0 := by
  ext i; fin_cases i <;>
    simp [nAv, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, SphereGeom.cross, cross_apply] <;> ring

private theorem AderivProof (D : Pt) (hoff : offAxis D) (t : ℝ) :
  HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D)
    (cross (nAv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D t)) t := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  have hnf : inner ℝ (nAv D) (EA D 0) = 0 := by
    change inner ℝ (nAv D) (unitDir (rawA D))=0
    rw [unitDir, real_inner_smul_right, ho, mul_zero]
  have hcross1 : cross (nAv D) (EA D 0) = EA D 1 := rfl
  have hcross2 : cross (nAv D) (EA D 1) = -(EA D 0) := by
    change cross (nAv D) (cross (nAv D) (EA D 0))=-(EA D 0)
    rw [cross_cross_native, hnf, hn]
    simp
  have hd : HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D)
      (rA D • ((-Real.sin t)•EA D 0 + Real.cos t•EA D 1)) t := by
    have hc := (Real.hasDerivAt_cos t).smul_const (EA D 0)
    have hs := (Real.hasDerivAt_sin t).smul_const (EA D 1)
    change HasDerivAt (fun z : ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D +
      rA D • (Real.cos z • EA D 0 + Real.sin z • EA D 1)) _ t
    exact ((hc.add hs).const_smul (rA D)).const_add (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)
  apply hd.congr_deriv
  simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, circlePt, cross_add_native,
    cross_center_A, cross_smul_native, hcross1, hcross2, zero_add]
  module

private theorem reflect_axis (D : Pt) : nAv (e-D)= -nBv D := by
  simp only [nAv, nBv, norm_sub_rev e D, smul_neg]

private theorem reflect_raw (D : Pt) : rawA (e-D)= -rawB D := by
  rw [rawA, reflect_axis, rawB]
  simp only [inner_neg_left, inner_neg_right, neg_smul, smul_neg]
  module

private theorem reflect_unit (D : Pt) : unitDir (rawA (e-D))= -unitDir (rawB D) := by
  rw [reflect_raw]
  simp [unitDir]

private theorem reflect_E0 (D : Pt) : EA (e-D) 0= -(EB D 0) := by
  simpa only [EA, EB, Matrix.cons_val_zero] using reflect_unit D

private theorem reflect_E1 (D : Pt) : EA (e-D) 1= -(EB D 1) := by
  change cross (nAv (e-D)) (unitDir (rawA (e-D)))=
    -(-cross (nBv D) (unitDir (rawB D)))
  rw [reflect_axis, reflect_unit, cross_neg_native, neg_neg]

private theorem reflect_center (D : Pt) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.cA (e-D)= -HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D := by
  simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, HardSphereB5.SphericalCrofton.Aux.MovingArc.cB]
  module

private theorem reflect_radius (D : Pt) : rA (e-D)=rB D := by
  simp only [rA, rB, norm_sub_rev e D]

private theorem reflect_cut (D : Pt) : cutA (e-D)=cutB D := by
  have he : inner ℝ (e:Pt) e=1 := by simp [real_inner_self_eq_norm_sq, e]
  simp only [cutA, cutB, reflect_radius, reflect_raw, norm_neg, inner_sub_left, he]
  congr 1
  ring

private theorem reflect_half (D : Pt) : halfA (e-D)=halfB D := by
  simp only [halfA, halfB, reflect_cut]

private theorem reflect_chart (D : Pt) (t : ℝ) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) t= -HardSphereB5.SphericalCrofton.Aux.MovingArc.v D t := by
  simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, HardSphereB5.SphericalCrofton.Aux.MovingArc.v,
    circlePt, reflect_center, reflect_E0, reflect_E1, reflect_radius]
  module

private theorem reflect_hypotheses (D : Pt) (hL : D∈LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D-e‖<1) :
    e-D∈LamC ∧ offAxis (e-D) ∧ Rc ‖e-D‖ ‖(e-D)-e‖<1 := by
  have hd : (e-D)-e = -D := by abel
  have hswap (a b : ℝ) : Rc a b=Rc b a := by
    unfold Rc
    have hprod : (a+b+1)*(a+b-1)*(a-b+1)*(-a+b+1)=
        (b+a+1)*(b+a-1)*(b-a+1)*(-b+a+1) := by ring
    rw [hprod, mul_comm a b]
  refine ⟨?_, ?_, ?_⟩
  · have hh : ‖D‖≤1 ∧ ‖D-e‖≤1 := by
      simpa only [LamC, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
        dist_eq_norm, sub_zero] using hL
    simpa only [LamC, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
      dist_eq_norm, sub_zero, hd, norm_neg, norm_sub_rev e D] using And.intro hh.2 hh.1
  · intro t ht
    apply hoff (1-t)
    calc
      D = e-(e-D) := by abel
      _ = e-t•e := by rw [ht]
      _ = (1-t)•e := by module
  · rw [norm_sub_rev e D, hd, norm_neg, hswap]
    exact hR

private theorem reflect_arc_mem (D : Pt) (hoff : offAxis D) (x : Pt) :
    x∈arcB D ↔ -x∈arcA (e-D) := by
  have hde : D≠e := by
    intro h
    exact hoff 1 (by simpa using h)
  have heD : e-D≠0 := sub_ne_zero.mpr (Ne.symm hde)
  have hs : (e-D)+(-x)= -(D+x-e) := by abel
  have ht : -(D+x-e)-e= -(D+x) := by abel
  simp only [arcA, arcB, if_neg hde, if_neg heD, Set.mem_setOf_eq, SigmaD,
    LamC, Set.mem_inter_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero, hs, ht, norm_neg]
  tauto

private theorem BgeometryProof (D : Pt)
  (hL : D ∈ LamC) (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1) :
  Orthonormal ℝ (EB D) ∧ 0 < rB D ∧
  0 < halfB D ∧ halfB D ≤ Real.pi ∧
  arcB D = HardSphereB5.SphericalCrofton.Aux.MovingArc.v D '' Set.Icc (-(halfB D)) (halfB D) ∧
  ∀ t : ℝ, HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D)
    (-cross (nBv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D t)) t := by
  rcases reflect_hypotheses D hL hoff hR with ⟨hLr,hoffr,hRr⟩
  have hframe := frameProof (e-D) hoffr
  have hhalf : 0<halfB D := by
    rw [← reflect_half, halfA]
    exact Real.arccos_pos.2 (cutBoundsProof (e-D) hLr hoffr hRr).2
  have hrB : 0<rB D := by
    rw [← reflect_radius]
    exact (movingA_radius (e-D) hLr).1
  refine ⟨?_, hrB, hhalf, Real.arccos_le_pi _, ?_, ?_⟩
  · rw [orthonormal_iff_ite] at hframe ⊢
    intro i j
    have hreflect (i : Fin 2) : EA (e-D) i= -(EB D i) := by
      fin_cases i
      · exact reflect_E0 D
      · exact reflect_E1 D
    simpa only [hreflect, inner_neg_left, inner_neg_right, neg_neg] using hframe i j
  · have ha := arcAProof (e-D) hLr hoffr hRr
    rw [reflect_half] at ha
    ext x
    rw [reflect_arc_mem D hoff, ha]
    constructor
    · rintro ⟨t,ht,hx⟩
      refine ⟨t,ht,?_⟩
      rw [reflect_chart] at hx
      exact neg_injective hx
    · rintro ⟨t,ht,hx⟩
      exact ⟨t,ht,by rw [reflect_chart,hx]⟩
  · intro t
    have hd := (AderivProof (e-D) hoffr t).neg
    change HasDerivAt (fun t => -HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) t)
      (-cross (nAv (e-D)) (HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) t)) t at hd
    have hf : (fun t => -HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) t)=
        HardSphereB5.SphericalCrofton.Aux.MovingArc.v D := by
      funext s
      rw [reflect_chart, neg_neg]
    rw [hf, reflect_axis, reflect_chart, cross_neg_native] at hd
    exact hd

private noncomputable def rotateFrame (E : Fin 2→Pt) (h : ℝ) : Fin 2→Pt :=
  ![Real.cos h • E 0 - Real.sin h • E 1,
    Real.sin h • E 0 + Real.cos h • E 1]

private theorem rotateFrame_orthonormal (E : Fin 2→Pt) (he : Orthonormal ℝ E) (h : ℝ) :
    Orthonormal ℝ (rotateFrame E h) := by
  have hinner := orthonormal_iff_ite.mp he
  have h00 : inner ℝ (E 0) (E 0)=1 := by simpa using hinner 0 0
  have h01 : inner ℝ (E 0) (E 1)=0 := by simpa using hinner 0 1
  have h10 : inner ℝ (E 1) (E 0)=0 := by simpa using hinner 1 0
  have h11 : inner ℝ (E 1) (E 1)=1 := by simpa using hinner 1 1
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · change inner ℝ (Real.cos h • E 0 - Real.sin h • E 1) (Real.cos h • E 0 - Real.sin h • E 1) = 1
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, h00,h01,h10,h11]
    nlinarith [Real.sin_sq_add_cos_sq h]
  · change inner ℝ (Real.cos h • E 0 - Real.sin h • E 1) (Real.sin h • E 0 + Real.cos h • E 1) = 0
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, h00,h01,h10,h11]
    nlinarith [Real.sin_sq_add_cos_sq h]
  · change inner ℝ (Real.sin h • E 0 + Real.cos h • E 1) (Real.cos h • E 0 - Real.sin h • E 1) = 0
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, h00,h01,h10,h11]
    nlinarith [Real.sin_sq_add_cos_sq h]
  · change inner ℝ (Real.sin h • E 0 + Real.cos h • E 1) (Real.sin h • E 0 + Real.cos h • E 1) = 1
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, h00,h01,h10,h11]
    nlinarith [Real.sin_sq_add_cos_sq h]

private theorem rotated_circle (c : Pt) (E : Fin 2→Pt) (r h t : ℝ) :
    circlePt c (rotateFrame E h 0) (rotateFrame E h 1) r t=
      circlePt c (E 0) (E 1) r (t-h) := by
  simp only [circlePt, rotateFrame, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.cos_sub, Real.sin_sub]
  module

private theorem shift_interval_image (f : ℝ→Pt) (h : ℝ) :
    f '' Set.Icc (-h) h = (fun t => f (t-h)) '' Set.Icc 0 (2*h) := by
  ext x
  constructor
  · rintro ⟨t,ht,htx⟩
    refine ⟨t+h,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    simpa only [add_sub_cancel_right] using htx
  · rintro ⟨t,ht,htx⟩
    exact ⟨t-h,⟨by linarith [ht.1],by linarith [ht.2]⟩,htx⟩

private theorem HardSphereB5.SphericalCrofton.Aux.MovingArc.isChart_exists (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) :
    ∃ C : HardSphereB5.SphericalCrofton.Aux.Santalo.Charts,
      HardSphereB5.SphericalCrofton.Aux.Santalo.IsChart D C := by
  let C : HardSphereB5.SphericalCrofton.Aux.Santalo.Charts := {
    oA := HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D,
    oB := HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D,
    EA := rotateFrame (EA D) (halfA D),
    EB := rotateFrame (EB D) (halfB D),
    TA := 2*halfA D,
    TB := 2*halfB D }
  have hAframe := frameProof D hoff
  have hAradius := (movingA_radius D hD).1
  have hAhalf : 0<halfA D := by
    rw [halfA]
    exact Real.arccos_pos.2 (cutBoundsProof D hD hoff hR).2
  rcases BgeometryProof D hD hoff hR with ⟨hBframe,hBradius,hBhalf,hBspan,hBimage,hBderiv⟩
  have hAu : HardSphereB5.SphericalCrofton.Aux.Santalo.u D C =
      fun t => HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (t-halfA D) := by
    funext t
    exact rotated_circle (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) (EA D) (rA D) (halfA D) t
  have hBv : HardSphereB5.SphericalCrofton.Aux.Santalo.v D C =
      fun t => HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (t-halfB D) := by
    funext t
    exact rotated_circle (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D) (EB D) (rB D) (halfB D) t
  refine ⟨C,?_,?_,hAradius,hBradius,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact rotateFrame_orthonormal _ hAframe _
  · exact rotateFrame_orthonormal _ hBframe _
  · change 0<2*halfA D
    linarith
  · change 0<2*halfB D
    linarith
  · change 2*halfA D≤2*Real.pi
    exact mul_le_mul_of_nonneg_left (Real.arccos_le_pi _) (by norm_num)
  · change 2*halfB D≤2*Real.pi
    exact mul_le_mul_of_nonneg_left hBspan (by norm_num)
  · change arcA D=HardSphereB5.SphericalCrofton.Aux.Santalo.u D C '' Set.Icc 0 (2*halfA D)
    rw [hAu,← shift_interval_image]
    exact arcAProof D hD hoff hR
  · change arcB D=HardSphereB5.SphericalCrofton.Aux.Santalo.v D C '' Set.Icc 0 (2*halfB D)
    rw [hBv,← shift_interval_image]
    exact hBimage
  · intro t
    rw [hAu]
    have hshift : HasDerivAt (fun s : ℝ => s-halfA D) (1 : ℝ) t :=
      (hasDerivAt_id t).sub_const (halfA D)
    have hc := (AderivProof D hoff (t-halfA D)).scomp t hshift
    simpa only [Function.comp_def, one_smul] using hc
  · intro t
    rw [hBv]
    have hshift : HasDerivAt (fun s : ℝ => s-halfB D) (1 : ℝ) t :=
      (hasDerivAt_id t).sub_const (halfB D)
    have hc := (hBderiv (t-halfB D)).scomp t hshift
    simpa only [Function.comp_def, one_smul] using hc
private theorem SphereGeom.Aux.ArcLength.chord_eq (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e) (r : ℝ) (hr : 0 < r) (s t : ℝ) :
    dist (circlePt c (e 0) (e 1) r s) (circlePt c (e 0) (e 1) r t) =
      2 * r * |Real.sin ((s - t) / 2)| := by
  have hi : inner ℝ ((Real.cos s - Real.cos t) • e 0)
      ((Real.sin s - Real.sin t) • e 1) = 0 := by
    simp [inner_smul_left, inner_smul_right, he.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)]
  have hsub : circlePt c (e 0) (e 1) r s - circlePt c (e 0) (e 1) r t =
      r • ((Real.cos s - Real.cos t) • e 0 + (Real.sin s - Real.sin t) • e 1) := by
    unfold circlePt
    module
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    ((Real.cos s - Real.cos t) • e 0) ((Real.sin s - Real.sin t) • e 1) hi
  simp only [norm_smul, Real.norm_eq_abs, he.norm_eq_one, mul_one, ← pow_two, sq_abs] at hn
  have htrig : (Real.cos s - Real.cos t) ^ 2 + (Real.sin s - Real.sin t) ^ 2 =
      4 * Real.sin ((s - t) / 2) ^ 2 := by
    have h1 := Real.sin_sq_add_cos_sq s
    have h2 := Real.sin_sq_add_cos_sq t
    have h3 := Real.cos_sub s t
    have h4 := Real.cos_two_mul ((s - t) / 2)
    have h5 := Real.sin_sq_add_cos_sq ((s - t) / 2)
    rw [show 2 * ((s - t) / 2) = s - t by ring] at h4
    nlinarith
  have hn2 : ‖(Real.cos s - Real.cos t) • e 0 + (Real.sin s - Real.sin t) • e 1‖ =
      2 * |Real.sin ((s - t) / 2)| := by
    nlinarith [sq_abs (Real.sin ((s - t) / 2)),
      norm_nonneg ((Real.cos s - Real.cos t) • e 0 + (Real.sin s - Real.sin t) • e 1),
      abs_nonneg (Real.sin ((s - t) / 2))]
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hn2]
  ring
open MeasureTheory SphereGeom

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_cap_domains (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D)) :
    ∃ (C : CircleEndpointAtlas) (F : Set Pt),
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
        ‖cross (if i = 0 then nAv D else nBv D) (atlasCircle C i t)‖ = C.r i) := by
  classical
  let P : CircleEndpointAtlas → Set Pt → Prop := fun C F =>
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
        ‖cross (if i = 0 then nAv D else nBv D) (atlasCircle C i t)‖ = C.r i)
  change ∃ C F, P C F
  have seam (c : Pt) (E : Fin 2 → Pt) (he : Orthonormal ℝ E) (r T : ℝ)
      (hr : 0 < r) (hT0 : 0 ≤ T) (hT : T ≤ 2*Real.pi) :
      circlePt c (E 0) (E 1) r '' Set.Ioo 0 T =
        (circlePt c (E 0) (E 1) r '' Set.Icc 0 T) \
          {circlePt c (E 0) (E 1) r 0, circlePt c (E 0) (E 1) r T} := by
    let f : ℝ → Pt := circlePt c (E 0) (E 1) r
    have hedge (t : ℝ) (ht : t ∈ Set.Ioo 0 T) (s : ℝ) (hs : s ∈ Set.Icc 0 T) :
        f t = f s → t = s := by
      intro heq
      have hd : 2*r*|Real.sin ((t-s)/2)| = 0 := by
        rw [← SphereGeom.Aux.ArcLength.chord_eq c E he r hr t s]
        change dist (f t) (f s) = 0
        rw [heq,dist_self]
      have hz : Real.sin ((t-s)/2) = 0 :=
        abs_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left (by positivity : 2*r ≠ 0))
      have h := (Real.sin_eq_zero_iff_of_lt_of_lt
        (by linarith [ht.1,hs.2] : -Real.pi < (t-s)/2)
        (by linarith [ht.2,hs.1] : (t-s)/2 < Real.pi)).mp hz
      linarith
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      refine ⟨⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩,?_⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
      constructor
      · intro heq
        have h := hedge t ht 0 ⟨le_rfl,hT0⟩ heq
        linarith [ht.1]
      · intro heq
        have h := hedge t ht T ⟨hT0,le_rfl⟩ heq
        linarith [ht.2]
    · rintro ⟨⟨t,ht,rfl⟩,hz⟩
      have ht0 : t ≠ 0 := by intro h; apply hz; rw [h]; exact Set.mem_insert _ _
      have htT : t ≠ T := by intro h; apply hz; rw [h]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      exact ⟨t,⟨lt_of_le_of_ne ht.1 ht0.symm,lt_of_le_of_ne ht.2 htT⟩,rfl⟩
  have speed (c : Pt) (E : Fin 2 → Pt) (he : Orthonormal ℝ E) (r : ℝ)
      (hr : 0 < r) (t : ℝ) : ‖deriv (circlePt c (E 0) (E 1) r) t‖ = r := by
    have hd : HasDerivAt (circlePt c (E 0) (E 1) r)
        (r • ((-Real.sin t) • E 0 + Real.cos t • E 1)) t := by
      exact ((((Real.hasDerivAt_cos t).smul_const (E 0)).add
        ((Real.hasDerivAt_sin t).smul_const (E 1))).const_smul r).const_add c
    rw [hd.deriv]
    have h00 : inner ℝ (E 0) (E 0) = 1 := by simpa using orthonormal_iff_ite.mp he 0 0
    have h01 : inner ℝ (E 0) (E 1) = 0 := by simpa using orthonormal_iff_ite.mp he 0 1
    have h10 : inner ℝ (E 1) (E 0) = 0 := by simpa using orthonormal_iff_ite.mp he 1 0
    have h11 : inner ℝ (E 1) (E 1) = 1 := by simpa using orthonormal_iff_ite.mp he 1 1
    have hsq : ‖(-Real.sin t) • E 0 + Real.cos t • E 1‖^2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
        h00,h01,h10,h11,mul_one,mul_zero,zero_mul,add_zero,zero_add]
      nlinarith [Real.sin_sq_add_cos_sq t]
    have hn : ‖(-Real.sin t) • E 0 + Real.cos t • E 1‖ = 1 := by
      nlinarith [norm_nonneg ((-Real.sin t) • E 0 + Real.cos t • E 1)]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
  have assemble (C : CircleEndpointAtlas) (F : Set Pt)
      (hF : F.Finite)
      (hc0 : C.c 0 = (-(1/2 : ℝ)) • D) (hc1 : C.c 1 = (1/2 : ℝ) • (e-D))
      (hr0 : C.r 0 = Real.sqrt (1 - ‖D‖^2/4)) (hr1 : C.r 1 = Real.sqrt (1 - ‖D-e‖^2/4))
      (hE : ∀ i, Orthonormal ℝ (C.frame i)) (hr : ∀ i, 0 < C.r i)
      (hT0 : ∀ i, 0 ≤ C.T i) (hT : ∀ i, C.T i ≤ 2*Real.pi)
      (hclosed : ∀ i : Fin 2,
        (C.T i = 0 ∧ (if i = 0 then arcA D else arcB D) = ∅) ∨
        ((if i = 0 then arcA D else arcB D) = atlasCircle C i '' Set.Icc 0 (C.T i) ∧
          F = {atlasCircle C i 0,atlasCircle C i (C.T i)}))
      (hAB : arcA D ∩ arcB D ⊆ F)
      (hfront : sFrontier (SigmaD D) = arcA D ∪ arcB D)
      (hder : ∀ (i : Fin 2) t, t ∈ Set.Ioo 0 (C.T i) → HasDerivAt (atlasCircle C i)
        (if i = 0 then cross (nAv D) (atlasCircle C i t)
         else -cross (nBv D) (atlasCircle C i t)) t) : P C F := by
    refine ⟨hF,hc0,hc1,hr0,hr1,hE,hr,hT0,hT,?_,hAB,?_,?_⟩
    · intro i
      rcases hclosed i with ⟨hzero,hempty⟩ | ⟨himage,hends⟩
      · rw [hzero,hempty,Set.Ioo_self,Set.image_empty,Set.empty_sdiff]
      · rw [himage,hends]
        exact seam (C.c i) (C.frame i) (hE i) (C.r i) (C.T i) (hr i) (hT0 i) (hT i)
    · rw [hfront]
    · intro i t ht
      refine ⟨hder i t ht,?_⟩
      have hn := speed (C.c i) (C.frame i) (hE i) (C.r i) (hr i) t
      change ‖deriv (atlasCircle C i) t‖ = C.r i at hn
      rw [(hder i t ht).deriv] at hn
      fin_cases i
      · exact hn
      · simpa using hn
  let B : Fin 2 → Pt := ![EuclideanSpace.single 1 1, -(EuclideanSpace.single 2 1)]
  let G : Fin 2 → Pt := rotateFrame B Real.pi
  have hB3 : Orthonormal ℝ ![B 0,B 1,e] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [B,e,PiLp.inner_apply,Fin.sum_univ_succ,EuclideanSpace.single_apply]
  have hB : Orthonormal ℝ B := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [B,PiLp.inner_apply,Fin.sum_univ_succ,EuclideanSpace.single_apply]
  have hG : Orthonormal ℝ G := rotateFrame_orthonormal B hB Real.pi
  let R : ℝ := Real.sqrt (3/4)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRsq : R^2 = 3/4 := Real.sq_sqrt (by norm_num)
  have heNorm : ‖(e : Pt)‖ = 1 := by simp [e]
  have heInner : inner ℝ (e : Pt) e = 1 := by simp [e,real_inner_self_eq_norm_sq]
  have fullSingle (h : ℝ) (hh : h^2 = 1/4) :
      (circlePt (h • e) (G 0) (G 1) R '' Set.Icc 0 (2*Real.pi) =
        {z : Pt | ‖z‖=1 ∧ inner ℝ e z = h}) ∧
      (∀ t, HasDerivAt (circlePt (h • e) (G 0) (G 1) R)
        (-cross e (circlePt (h • e) (G 0) (G 1) R t)) t) := by
    have himg := fullCircleImage (B 0) (B 1) e hB3
    let f : ℝ → Pt := circlePt (h • e) (G 0) (G 1) R
    have hshape (t : ℝ) : f t = h • e + R • circlePt 0 (B 0) (B 1) 1 (t-Real.pi) := by
      rw [show f t = circlePt (h • e) (G 0) (G 1) R t from rfl]
      rw [show G = rotateFrame B Real.pi from rfl,rotated_circle]
      simp [circlePt]
    constructor
    · ext z
      constructor
      · rintro ⟨t,ht,rfl⟩
        have hy : circlePt 0 (B 0) (B 1) 1 (t-Real.pi) ∈ greatCircle e := by
          rw [← himg]
          exact ⟨t-Real.pi,⟨by linarith [ht.1],by linarith [ht.2]⟩,rfl⟩
        change ‖f t‖=1 ∧ inner ℝ e (f t)=h
        rw [hshape]
        refine ⟨?_,?_⟩
        · have hsq : ‖h • e + R • circlePt 0 (B 0) (B 1) 1 (t-Real.pi)‖^2 = 1 := by
            rw [norm_add_sq_real]
            simp only [norm_smul,Real.norm_eq_abs,heNorm,hy.1,real_inner_smul_left,
              real_inner_smul_right,hy.2,mul_zero,mul_one,zero_add,add_zero,
              abs_of_pos hRpos,sq_abs]
            nlinarith
          nlinarith [norm_nonneg (h • e + R • circlePt 0 (B 0) (B 1) 1 (t-Real.pi))]
        · rw [inner_add_right,real_inner_smul_right,real_inner_smul_right,heInner,hy.2]
          ring
      · rintro ⟨hz,hze⟩
        let y : Pt := R⁻¹ • (z-h • e)
        have hyn : ‖y‖ = 1 := by
          have hinnerze : inner ℝ z e = h := by rw [real_inner_comm]; exact hze
          have hsubsq : ‖z-h • e‖^2 = R^2 := by
            rw [norm_sub_sq_real,hz]
            simp only [norm_smul,Real.norm_eq_abs,heNorm,mul_one,real_inner_smul_right,
              hinnerze,sq_abs]
            nlinarith [hh,hRsq]
          have hnsub : ‖z-h • e‖ = R := by nlinarith [norm_nonneg (z-h • e)]
          simp [y,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hRpos,hnsub,
            inv_mul_cancel₀ hRpos.ne']
        have hye : inner ℝ e y = 0 := by
          simp only [y,real_inner_smul_right,inner_sub_right,hze,heInner,mul_one,
            sub_self,mul_zero]
        have hy : y ∈ greatCircle e := ⟨hyn,hye⟩
        rw [← himg] at hy
        obtain ⟨s,hs,hsy⟩ := hy
        refine ⟨s+Real.pi,⟨by linarith [hs.1],by linarith [hs.2]⟩,?_⟩
        change f (s+Real.pi) = z
        rw [hshape,add_sub_cancel_right,hsy]
        simp [y,smul_smul,mul_inv_cancel₀ hRpos.ne']
    · intro t
      have hd : HasDerivAt f (R • ((-Real.sin t) • G 0 + Real.cos t • G 1)) t :=
        ((((Real.hasDerivAt_cos t).smul_const (G 0)).add
          ((Real.hasDerivAt_sin t).smul_const (G 1))).const_smul R).const_add (h • e)
      apply hd.congr_deriv
      ext i
      fin_cases i <;> simp [f,circlePt,G,B,rotateFrame,e,SphereGeom.cross,cross_apply,
        EuclideanSpace.single_apply] <;> ring
  by_cases hDzero : D = 0
  · subst D
    let C : CircleEndpointAtlas := { c := ![0,(1/2 : ℝ) • e],frame := ![B,G],r := ![1,R],T := ![0,2*Real.pi] }
    let F : Set Pt := {atlasCircle C 1 0,atlasCircle C 1 (C.T 1)}
    have hsingle := fullSingle (1/2) (by norm_num)
    refine ⟨C,F,assemble C F (Set.toFinite _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · simp [C]
    · simp [C]
    · simp [C]
    · norm_num [C,R,e]
    · intro i; fin_cases i; exact hB; exact hG
    · intro i; fin_cases i; norm_num [C]; exact hRpos
    · intro i; fin_cases i <;> simp [C,Real.pi_pos.le]
    · intro i; fin_cases i <;> simp [C,Real.pi_pos.le]
    · intro i; fin_cases i
      · exact Or.inl ⟨rfl,sigma_axis_cases.2.1.2.1⟩
      · right
        refine ⟨?_,rfl⟩
        simpa [atlasCircle,C] using! sigma_axis_cases.2.1.2.2.trans hsingle.1.symm
    · simp [sigma_axis_cases.2.1.2.1]
    · rw [sigma_axis_cases.2.1.1,sigma_axis_cases.2.1.2.1,Set.empty_union,sigma_axis_cases.2.1.2.2]
      exact HardSphereB5.SphericalCrofton.Aux.Cap.frontier_slice e heNorm (1/2) (by norm_num) (by norm_num)
    · intro i t ht; fin_cases i
      · simp [C] at ht
      · simpa [atlasCircle,C,nBv,e,Real.norm_eq_abs] using! hsingle.2 t
  by_cases hDe : D = e
  · subst D
    let C : CircleEndpointAtlas := { c := ![(-(1/2 : ℝ)) • e,0],frame := ![G,B],r := ![R,1],T := ![2*Real.pi,0] }
    let F : Set Pt := {atlasCircle C 0 0,atlasCircle C 0 (C.T 0)}
    have hsingle := fullSingle (-(1/2)) (by norm_num)
    have hArc : arcA e = circlePt (-(1/2 : ℝ) • e) (G 0) (G 1) R '' Set.Icc 0 (2*Real.pi) := by
      rw [sigma_axis_cases.2.2.2.2,hsingle.1]
      ext z
      simp only [Set.mem_setOf_eq,inner_neg_left]
      constructor <;> rintro ⟨hz,hi⟩ <;> refine ⟨hz,?_⟩ <;> linarith
    refine ⟨C,F,assemble C F (Set.toFinite _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · simp [C]
    · simp [C]
    · norm_num [C,R,e]
    · simp [C]
    · intro i; fin_cases i; exact hG; exact hB
    · intro i; fin_cases i; exact hRpos; norm_num [C]
    · intro i; fin_cases i <;> simp [C,Real.pi_pos.le]
    · intro i; fin_cases i <;> simp [C,Real.pi_pos.le]
    · intro i; fin_cases i
      · exact Or.inr ⟨hArc,rfl⟩
      · exact Or.inl ⟨rfl,sigma_axis_cases.2.2.2.1⟩
    · simp [sigma_axis_cases.2.2.2.1]
    · rw [sigma_axis_cases.2.2.1,sigma_axis_cases.2.2.2.1,Set.union_empty,sigma_axis_cases.2.2.2.2]
      exact HardSphereB5.SphericalCrofton.Aux.Cap.frontier_slice (-e) (by simpa using heNorm) (1/2) (by norm_num) (by norm_num)
    · intro i t ht; fin_cases i
      · change HasDerivAt (circlePt ((-(1/2 : ℝ)) • e) (G 0) (G 1) R)
          (cross (nAv e) (circlePt ((-(1/2 : ℝ)) • e) (G 0) (G 1) R t)) t
        have hn : nAv e = -e := by simp [nAv,heNorm]
        rw [hn]
        apply (hsingle.2 t).congr_deriv
        ext j
        fin_cases j <;> simp [SphereGeom.cross,cross_apply] <;> ring
      · simp [C] at ht
  have hnon : ¬ (SigmaD D).Subsingleton := by
    intro hss
    obtain ⟨z,hz⟩ := hK.interior_nonempty
    rcases hz with ⟨w,hw,rfl⟩
    have hwNorm : ‖(w : Pt)‖ = 1 := by simpa [Metric.mem_sphere,dist_zero_right] using w.property
    obtain ⟨F1,F2,hF1,hF2,hFrame⟩ := SphereGeom.exists_measurable_frame
    let z : Pt := w
    let q : Pt := F1 z
    have hFr := hFrame z hwNorm
    have hqnorm : ‖q‖ = 1 := by simpa [q] using hFr.norm_eq_one (0 : Fin 3)
    have hqz : inner ℝ q z = 0 := by
      simpa [q] using hFr.inner_eq_zero (show (0 : Fin 3) ≠ 2 by decide)
    let f : ℝ → Pt := fun t => Real.cos t • z + Real.sin t • q
    have hzNorm : ‖z‖ = 1 := hwNorm
    have hzq : inner ℝ z q = 0 := by rw [real_inner_comm]; exact hqz
    have hfnorm (t : ℝ) : ‖f t‖ = 1 := by
      have hs : ‖f t‖^2 = 1 := by
        dsimp only [f]
        rw [norm_add_sq_real]
        simp only [norm_smul,Real.norm_eq_abs,hzNorm,hqnorm,mul_one,real_inner_smul_left,
          real_inner_smul_right,hzq,mul_zero,zero_add,add_zero,sq_abs]
        nlinarith [Real.cos_sq_add_sin_sq t]
      nlinarith [norm_nonneg (f t)]
    let g : ℝ → Metric.sphere (0 : Pt) 1 := fun t => ⟨f t,by simpa [Metric.mem_sphere,dist_zero_right] using hfnorm t⟩
    have hg : Continuous g := by
      apply Continuous.subtype_mk
      dsimp [f]
      fun_prop
    have hg0 : g 0 = w := by apply Subtype.ext; simp [g,f,z]
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), g t ∈ interior ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' SigmaD D) := by
      apply hg.continuousAt.eventually
      rw [hg0]
      exact isOpen_interior.mem_nhds hw
    have h1 := hnear.filter_mono (show 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have h2 : ∀ᶠ t in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < t := self_mem_nhdsWithin
    have h3 : ∀ᶠ t in 𝓝[Set.Ioi (0 : ℝ)] 0, t < Real.pi :=
      (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds
    obtain ⟨t,⟨htK,ht0⟩,htπ⟩ := ((h1.and h2).and h3).exists
    have hft : f t ∈ SigmaD D := by
      have htmem : g t ∈ (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' SigmaD D := interior_subset htK
      exact htmem
    have hzK : z ∈ SigmaD D := by
      have hwmem : w ∈ (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' SigmaD D := interior_subset hw
      exact hwmem
    have heq : f t = z := hss hft hzK
    have hi := congrArg (fun y => inner ℝ q y) heq
    simp only [f,inner_add_right,real_inner_smul_right,hqz,real_inner_self_eq_norm_sq,hqnorm,
      one_pow,mul_one,mul_zero,zero_add] at hi
    have hsin := Real.sin_pos_of_pos_of_lt_pi ht0 htπ
    linarith
  have hoff : offAxis D := by
    intro t ht
    have hnorms : ‖D‖ ≤ 1 ∧ ‖D-e‖ ≤ 1 := by simpa [LamC,Metric.mem_closedBall,dist_eq_norm] using hD
    have hn0 : |t| ≤ 1 := by simpa [ht,norm_smul,Real.norm_eq_abs,heNorm] using hnorms.1
    have hne : |t-1| ≤ 1 := by
      have hdiff : t • e - e = (t-1) • e := by module
      simpa [ht,hdiff,norm_smul,Real.norm_eq_abs,heNorm] using hnorms.2
    have ht0 : 0 < t := by
      have hge : 0 ≤ t := by linarith [(abs_le.mp hne).1]
      apply lt_of_le_of_ne hge
      intro h0
      apply hDzero
      simp [ht,← h0]
    have ht1 : t < 1 := by
      have hle : t ≤ 1 := (abs_le.mp hn0).2
      apply lt_of_le_of_ne hle
      intro h1
      apply hDe
      simp [ht,h1]
    have hempty := sigma_axis_cases.1 t ht0 ht1
    rw [← ht] at hempty
    apply hnon
    rw [hempty]
    exact Set.subsingleton_empty
  have hRc : Rc ‖D‖ ‖D-e‖ < 1 := by
    have hs := sigma_support D hD hoff
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hgt | heq
    · apply hnon
      rw [hs.2.2 hgt]
      exact Set.subsingleton_empty
    · obtain ⟨V,hV⟩ := hs.2.1 heq.symm
      apply hnon
      rw [hV]
      exact Set.subsingleton_singleton
  let C : CircleEndpointAtlas := {
    c := ![HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D,HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D]
    frame := ![rotateFrame (EA D) (halfA D),rotateFrame (EB D) (halfB D)]
    r := ![HardSphereB5.SphericalCrofton.Aux.MovingArc.rA D,HardSphereB5.SphericalCrofton.Aux.MovingArc.rB D]
    T := ![2*halfA D,2*halfB D] }
  let F : Set Pt := vertsD D
  have hAf := frameProof D hoff
  have hAr := (movingA_radius D hD).1
  have hAh : 0 < halfA D := Real.arccos_pos.2 (cutBoundsProof D hD hoff hRc).2
  rcases BgeometryProof D hD hoff hRc with ⟨hBf,hBr,hBh,hBhπ,hBi,hBd⟩
  have hC0 (t : ℝ) : atlasCircle C 0 t = HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (t-halfA D) :=
    rotated_circle _ _ _ _ _
  have hC1 (t : ℝ) : atlasCircle C 1 t = HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (t-halfB D) :=
    rotated_circle _ _ _ _ _
  have hArc0 : arcA D = atlasCircle C 0 '' Set.Icc 0 (C.T 0) := by
    change arcA D = atlasCircle C 0 '' Set.Icc 0 (2*halfA D)
    simp_rw [hC0]
    rw [← shift_interval_image]
    exact arcAProof D hD hoff hRc
  have hArc1 : arcB D = atlasCircle C 1 '' Set.Icc 0 (C.T 1) := by
    change arcB D = atlasCircle C 1 '' Set.Icc 0 (2*halfB D)
    simp_rw [hC1]
    rw [← shift_interval_image]
    exact hBi
  have hF0 : F = {atlasCircle C 0 0,atlasCircle C 0 (C.T 0)} := by
    rw [hC0,hC0]
    change vertsD D = {HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (0-halfA D),HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (2*halfA D-halfA D)}
    simpa only [zero_sub,show 2*halfA D-halfA D = halfA D by ring] using
      HardSphereB5.SphericalCrofton.Aux.MovingArc.endpointsA D hD hoff hRc
  have hvertsReflect (z : Pt) : z ∈ vertsD D ↔ -z ∈ vertsD (e-D) := by
    have hs : (e-D)+(-z) = -(D+z-e) := by abel
    have ht : -(D+z-e)-e = -(D+z) := by abel
    simp only [vertsD,Set.mem_setOf_eq,norm_neg,hs,ht,dist_eq_norm]
    tauto
  have hF1 : F = {atlasCircle C 1 0,atlasCircle C 1 (C.T 1)} := by
    rcases reflect_hypotheses D hD hoff hRc with ⟨hLr,hoffr,hRr⟩
    have ha := HardSphereB5.SphericalCrofton.Aux.MovingArc.endpointsA (e-D) hLr hoffr hRr
    rw [reflect_half] at ha
    ext z
    change z ∈ vertsD D ↔ z ∈ {atlasCircle C 1 0,atlasCircle C 1 (2*halfB D)}
    rw [hvertsReflect,ha,hC1,hC1]
    simp only [reflect_chart,zero_sub,show 2*halfB D-halfB D = halfB D by ring,
      Set.mem_insert_iff,Set.mem_singleton_iff,neg_inj]
  have hAB : arcA D ∩ arcB D ⊆ F := by
    intro z hz
    have hA : z ∈ SigmaD D ∧ ‖D+z‖=1 := by simpa [arcA,hDzero] using hz.1
    have hB : z ∈ SigmaD D ∧ dist (D+z) e=1 := by simpa [arcB,hDe] using hz.2
    exact ⟨hA.1.1,hA.2,hB.2⟩
  have hfront : sFrontier (SigmaD D) = arcA D ∪ arcB D := by
    apply Set.Subset.antisymm (HardSphereB5.SphericalCrofton.Aux.frontierSigma_subset_arcs D)
    have hnorms : ‖D‖≤1 ∧ ‖D-e‖≤1 := by simpa [LamC,Metric.mem_closedBall,dist_eq_norm] using hD
    rcases HardSphereB5.SphericalCrofton.Aux.Cap.sigma_caps_data D hDzero hDe with ⟨hna,hnb,hcaps⟩
    have hfmono (H : Set Pt) (hsub : SigmaD D ⊆ H) (z : Pt) (hz : z ∈ SigmaD D)
        (hfrontz : z ∈ sFrontier H) : z ∈ sFrontier (SigmaD D) := by
      rcases hfrontz with ⟨w,hw,rfl⟩
      refine ⟨w,⟨subset_closure hz,?_⟩,rfl⟩
      intro hi
      exact hw.2 (interior_mono (Set.preimage_mono hsub) hi)
    intro z hz
    rcases hz with hzA | hzB
    · have hzA' : z ∈ SigmaD D ∧ ‖D+z‖=1 := by simpa [arcA,hDzero] using hzA
      have hinner : inner ℝ (nAv D) z = ‖D‖/2 := by
        have hs := norm_add_sq_real D z
        rw [hzA'.1.1,hzA'.2] at hs
        have hi : inner ℝ D z = -(‖D‖^2)/2 := by nlinarith
        simp only [nAv,real_inner_smul_left,inner_neg_left,hi]
        field_simp [norm_ne_zero_iff.mpr hDzero]
      apply hfmono (cap (nAv D) (‖D‖/2))
        (by rw [hcaps]; exact Set.inter_subset_left) z hzA'.1
      rw [HardSphereB5.SphericalCrofton.Aux.Cap.frontier_slice (nAv D) hna (‖D‖/2)
        (by positivity) (by linarith [hnorms.1])]
      exact ⟨hzA'.1.1,hinner⟩
    · have hzB' : z ∈ SigmaD D ∧ dist (D+z) e=1 := by simpa [arcB,hDe] using hzB
      have hnormdiff : ‖(e-D)-z‖=1 := by
        have hvec : (e-D)-z = -(D+z-e) := by abel
        rw [hvec,norm_neg]
        exact (by simpa only [dist_eq_norm] using hzB'.2)
      have hinner : inner ℝ (nBv D) z = ‖D-e‖/2 := by
        have hs := norm_sub_sq_real (e-D) z
        rw [hzB'.1.1,hnormdiff,norm_sub_rev e D] at hs
        have hi : inner ℝ (e-D) z = ‖D-e‖^2/2 := by nlinarith
        simp only [nBv,real_inner_smul_left,hi]
        field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hDe)]
      apply hfmono (cap (nBv D) (‖D-e‖/2))
        (by rw [hcaps]; exact Set.inter_subset_right) z hzB'.1
      rw [HardSphereB5.SphericalCrofton.Aux.Cap.frontier_slice (nBv D) hnb (‖D-e‖/2)
        (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hDe)) (by norm_num)) (by linarith [hnorms.2])]
      exact ⟨hzB'.1.1,hinner⟩
  refine ⟨C,F,assemble C F (by rw [hF0]; exact Set.toFinite _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hAB hfront ?_⟩
  · norm_num [C,HardSphereB5.SphericalCrofton.Aux.MovingArc.cA]
  · rfl
  · rfl
  · rfl
  · intro i; fin_cases i
    · exact rotateFrame_orthonormal _ hAf _
    · exact rotateFrame_orthonormal _ hBf _
  · intro i; fin_cases i; exact hAr; exact hBr
  · intro i; fin_cases i; exact (mul_pos (by norm_num) hAh).le; exact (mul_pos (by norm_num) hBh).le
  · intro i; fin_cases i
    · exact mul_le_mul_of_nonneg_left (Real.arccos_le_pi _) (by norm_num)
    · exact mul_le_mul_of_nonneg_left hBhπ (by norm_num)
  · intro i; fin_cases i
    · exact Or.inr ⟨hArc0,hF0⟩
    · exact Or.inr ⟨hArc1,hF1⟩
  · intro i t ht; fin_cases i
    · change HasDerivAt (atlasCircle C 0) (cross (nAv D) (atlasCircle C 0 t)) t
      rw [show atlasCircle C 0 = (fun s => HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (s-halfA D)) from funext hC0]
      have hh := (AderivProof D hoff (t-halfA D)).scomp t ((hasDerivAt_id t).sub_const (halfA D))
      simpa only [Function.comp_def,id_eq,one_smul] using! hh
    · change HasDerivAt (atlasCircle C 1) (-cross (nBv D) (atlasCircle C 1 t)) t
      rw [show atlasCircle C 1 = (fun s => HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (s-halfB D)) from funext hC1]
      have hh := (hBd (t-halfB D)).scomp t ((hasDerivAt_id t).sub_const (halfB D))
      simpa only [Function.comp_def,id_eq,one_smul] using! hh

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_endpoint_cap_domains
