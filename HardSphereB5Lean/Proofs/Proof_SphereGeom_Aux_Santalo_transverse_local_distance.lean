import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom Asymptotics Filter
open scoped Topology
noncomputable section

private lemma cross_linear_zero (a b : E3) (x y : ℝ) :
    cross (x • a - y • b) b = x • cross a b := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring

private lemma cross_right_zero (a : E3) : cross a 0 = 0 := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply]

theorem proof_SphereGeom_Aux_Santalo_transverse_local_distance (U V : ℝ → E3) (U' V' : E3) (a b : ℝ)
    (hU : HasDerivAt U U' a) (hV : HasDerivAt V V' b)
    (heq : U a = V b) (hcross : cross U' V' ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℝ × ℝ in 𝓝 (a, b),
      c * ‖z - (a, b)‖ ≤ ‖U z.1 - V z.2‖ := by
  let L : (ℝ × ℝ) →L[ℝ] E3 :=
    (ContinuousLinearMap.toSpanSingleton ℝ U').comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
    (ContinuousLinearMap.toSpanSingleton ℝ V').comp (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hL (z : ℝ × ℝ) : L z = z.1 • U' - z.2 • V' := by simp [L]
  have hker : L.toLinearMap.ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    change L z = 0 at hz
    rw [hL] at hz
    have hcz := congrArg (fun w => cross w V') hz
    rw [cross_linear_zero] at hcz
    have hc0 : cross (0 : E3) V' = 0 := by ext i; fin_cases i <;> simp [cross, cross_apply]
    rw [hc0] at hcz
    have hz1 : z.1 = 0 := (smul_eq_zero.mp hcz).resolve_right hcross
    have hvne : V' ≠ 0 := by intro h; exact hcross (by rw [h, cross_right_zero])
    have hz2 : z.2 = 0 := by
      simp only [hz1, zero_smul, zero_sub, neg_eq_zero] at hz
      exact (smul_eq_zero.mp hz).resolve_right hvne
    exact Prod.ext hz1 hz2
  have hfst : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (a, b) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (a, b) := hasFDerivAt_snd
  have hu := hU.hasFDerivAt.comp (a, b) hfst
  have hv := hV.hasFDerivAt.comp (a, b) hsnd
  have hf : HasFDerivAt (fun z : ℝ × ℝ => U z.1 - V z.2) L (a, b) := by
    exact hu.sub hv
  obtain ⟨K, hKpos, hK⟩ := L.toLinearMap.exists_antilipschitzWith hker
  have hA : (fun z : ℝ × ℝ => z - (a, b)) =O[𝓝 (a, b)]
      (fun z => L (z - (a, b))) := by
    apply isBigO_iff.mpr
    exact ⟨K, Eventually.of_forall (fun z => by simpa using hK.le_mul_dist (z - (a, b)) 0)⟩
  have hAs : (fun z : ℝ × ℝ => U z.1 - V z.2 - (U a - V b)) ~[𝓝 (a, b)]
      (fun z => L (z - (a, b))) := hf.isLittleO.trans_isBigO hA
  have hB := hA.trans hAs.isBigO_symm
  obtain ⟨C, hC⟩ := isBigO_iff.mp hB
  let M : ℝ := |C| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M⁻¹, inv_pos.mpr hM, ?_⟩
  filter_upwards [hC] with z hz
  have hbound : ‖z - (a, b)‖ ≤ M * ‖U z.1 - V z.2‖ := by
    simpa [heq, sub_self, sub_zero] using
      hz.trans (mul_le_mul_of_nonneg_right (by dsimp [M]; linarith [le_abs_self C]) (norm_nonneg _))
  calc
    M⁻¹ * ‖z - (a, b)‖ ≤ M⁻¹ * (M * ‖U z.1 - V z.2‖) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hM.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul]
