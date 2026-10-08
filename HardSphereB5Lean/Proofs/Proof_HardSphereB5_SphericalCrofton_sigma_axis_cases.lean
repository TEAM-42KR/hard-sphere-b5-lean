import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_sigma_axis_cases :
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

