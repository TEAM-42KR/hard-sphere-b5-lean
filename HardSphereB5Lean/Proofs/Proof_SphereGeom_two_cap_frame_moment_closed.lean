import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_two_cap_frame_transverse_closed
import HardSphereB5Lean.Theorems.Thm_SphereGeom_two_cap_normal_moment
set_option autoImplicit false
open MeasureTheory Real SphereGeom
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem proof_SphereGeom_two_cap_frame_moment_closed (e : Fin 3 → E3) (he : Orthonormal ℝ e) (A K L : ℝ) (hA0 : 0 < A) (hA2 : A < 2) (hL : 0 < L) (hB2 : K ^ 2 + L ^ 2 < 4) (hH : 0 < L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2) :
 let B := Real.sqrt (K ^ 2 + L ^ 2)
 let H := L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2
 (∫ u in cap (A • e 0) (A ^ 2 / 2) ∩ cap (K • e 0 + L • e 1) ((K ^ 2 + L ^ 2) / 2), u ∂dOmega) =
 (((1 - A ^ 2 / 4) * Complex.arg ⟨B ^ 2 - A * K, 2 * Real.sqrt H⟩ + ((1 - B ^ 2 / 4) * K / B) * Complex.arg ⟨B * (A - K), 2 * Real.sqrt H⟩ - Real.sqrt H / 2)) • e 0 +
 ((((1 - B ^ 2 / 4) * L / B) * Complex.arg ⟨B * (A - K), 2 * Real.sqrt H⟩ - Real.sqrt H * (A - K) / (2 * L))) • e 1 := by
  classical
  dsimp only
  set B := Real.sqrt (K ^ 2 + L ^ 2) with hBdef
  set H := L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2 with hHdef
  have hB0 : 0 < B := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg K])
  have hBn : B ≠ 0 := ne_of_gt hB0
  have hAn : A ≠ 0 := ne_of_gt hA0
  have hLn : L ≠ 0 := ne_of_gt hL
  have hBs : B ^ 2 = K ^ 2 + L ^ 2 := Real.sq_sqrt (by positivity)
  have hLsq : L ^ 2 = B ^ 2 - K ^ 2 := by linarith
  have hBt : B < 2 := by nlinarith
  have hAt : A ^ 2 < 4 := by nlinarith
  change 0 < H at hH
  let k := A * K / B
  let l := A * L / B
  let f : Fin 3 → E3 := ![(K / B) • e 0 + (L / B) • e 1,
    (L / B) • e 0 - (K / B) • e 1, e 2]
  have hei := orthonormal_iff_ite.mp he
  have hen := he.1
  have hf0def : f 0 = (K / B) • e 0 + (L / B) • e 1 := rfl
  have hf1def : f 1 = (L / B) • e 0 - (K / B) • e 1 := rfl
  have hf2def : f 2 = e 2 := rfl
  have hf : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [f, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right, hei] <;>
      norm_num [Fin.ext_iff] <;> field_simp [hBn] <;> nlinarith only [hBs]
  have hl : 0 < l := by dsimp [l]; positivity
  have hkl : k ^ 2 + l ^ 2 = A ^ 2 := by
    dsimp [k, l]
    field_simp
    nlinarith [hBs]
  have hkl4 : k ^ 2 + l ^ 2 < 4 := by rw [hkl]; exact hAt
  have hkcoef : k * (K / B) + l * (L / B) = A := by
    dsimp [k, l]
    field_simp
    nlinarith [hBs]
  have hlcoef : k * (L / B) - l * (K / B) = 0 := by dsimp [k, l]; ring
  have hf0 : B • f 0 = K • e 0 + L • e 1 := by
    dsimp [f]
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> field_simp
  have hf1 : k • f 0 + l • f 1 = A • e 0 := by
    calc
      k • f 0 + l • f 1 = (k * (K / B) + l * (L / B)) • e 0 +
        (k * (L / B) - l * (K / B)) • e 1 := by dsimp [f]; module
      _ = A • e 0 := by rw [hkcoef, hlcoef]; simp
  let Hs := l ^ 2 * (1 - B ^ 2 / 4) - ((k ^ 2 + l ^ 2) / 2 - k * B / 2) ^ 2
  have hHs : Hs = (A / B) ^ 2 * H := by
    dsimp only [Hs]
    rw [hkl]
    dsimp only [k, l]
    rw [hHdef, ← hBs]
    field_simp
    ring_nf
    rw [hLsq]
    ring
  have hHs0 : 0 < Hs := by rw [hHs]; positivity
  have hsqrt : Real.sqrt Hs = (A / B) * Real.sqrt H := by
    rw [hHs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt (div_pos hA0 hB0))]
  have hsB : Real.sqrt (k ^ 2 + l ^ 2) = A := by rw [hkl, Real.sqrt_sq hA0.le]
  let m := ∫ u in cap (A • e 0) (A ^ 2 / 2) ∩ cap (K • e 0 + L • e 1) ((K ^ 2 + L ^ 2) / 2), u ∂dOmega
  let α := Complex.arg (⟨B ^ 2 - A * K, 2 * Real.sqrt H⟩ : ℂ)
  let β := Complex.arg (⟨B * (A - K), 2 * Real.sqrt H⟩ : ℂ)
  let c0 := (1 - A ^ 2 / 4) * α + ((1 - B ^ 2 / 4) * K / B) * β - Real.sqrt H / 2
  let c1 := ((1 - B ^ 2 / 4) * L / B) * β - Real.sqrt H * (A - K) / (2 * L)
  change m = c0 • e 0 + c1 • e 1
  have hm1 := SphereGeom.two_cap_frame_transverse_closed e he A K L hA0 hA2 hL hB2 hH
  change inner ℝ (e 1) m = c1 at hm1
  have hsets : cap (B • f 0) (B ^ 2 / 2) ∩ cap (k • f 0 + l • f 1) ((k ^ 2 + l ^ 2) / 2) =
      cap (A • e 0) (A ^ 2 / 2) ∩ cap (K • e 0 + L • e 1) ((K ^ 2 + L ^ 2) / 2) := by
    rw [hf0, hf1, hkl, hBs, Set.inter_comm]
  have hmS := SphereGeom.two_cap_frame_transverse_closed f hf B k l hB0 hBt hl hkl4 hHs0
  simp only [hsets] at hmS
  change inner ℝ (f 1) m = ((1 - (Real.sqrt (k ^ 2 + l ^ 2)) ^ 2 / 4) * l / Real.sqrt (k ^ 2 + l ^ 2)) *
    Complex.arg ⟨Real.sqrt (k ^ 2 + l ^ 2) * (B - k), 2 * Real.sqrt Hs⟩ - Real.sqrt Hs * (B - k) / (2 * l) at hmS
  rw [hsB, hsqrt] at hmS
  have hcomplex : (⟨A * (B - k), 2 * ((A / B) * Real.sqrt H)⟩ : ℂ) =
      ((A / B : ℝ) : ℂ) * (⟨B ^ 2 - A * K, 2 * Real.sqrt H⟩ : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, k] <;> field_simp <;> ring
  rw [hcomplex, Complex.arg_real_mul _ (div_pos hA0 hB0)] at hmS
  change inner ℝ (f 1) m = ((1 - A ^ 2 / 4) * l / A) * α - ((A / B) * Real.sqrt H) * (B - k) / (2 * l) at hmS
  rw [hf1def, inner_sub_left, real_inner_smul_left, real_inner_smul_left] at hmS
  have hmS' : (L / B) * inner ℝ (e 0) m - (K / B) * inner ℝ (e 1) m =
      ((1 - A ^ 2 / 4) * L / B) * α - Real.sqrt H * (B ^ 2 - A * K) / (2 * B * L) := by
    rw [hmS]
    dsimp [k, l]
    field_simp <;> ring
  have hm0 : inner ℝ (e 0) m = c0 := by
    apply mul_left_cancel₀ (ne_of_gt (div_pos hL hB0))
    calc
      (L / B) * inner ℝ (e 0) m =
          ((1 - A ^ 2 / 4) * L / B) * α - Real.sqrt H * (B ^ 2 - A * K) / (2 * B * L) +
          (K / B) * inner ℝ (e 1) m := by linarith [hmS']
      _ = (L / B) * c0 := by
        rw [hm1]
        dsimp [c0, c1]
        field_simp
        ring_nf
        rw [hLsq]
        ring
  have hm2 : inner ℝ (e 2) m = 0 := SphereGeom.two_cap_normal_moment e he A K L (A ^ 2 / 2) ((K ^ 2 + L ^ 2) / 2)
  let b := basisOfOrthonormalOfCardEqFinrank he (by simp [E3])
  have hb : Orthonormal ℝ b := by simpa [b] using he
  let ob := b.toOrthonormalBasis hb
  have hob (i : Fin 3) : ob i = e i := by simp [ob, b]
  have hmrepr := ob.sum_repr' m
  simpa only [Fin.sum_univ_three, hob, hm0, hm1, hm2, zero_smul, add_zero] using hmrepr.symm
