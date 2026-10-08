import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Cap_strict_midpoint
    (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hpos : ∀ i, 0 < h i) (u v : Pt) (hus : ‖u‖ = 1) (hvs : ‖v‖ = 1)
    (hu : ∀ i, h i ≤ inner ℝ (n i) u) (hv : ∀ i, h i ≤ inner ℝ (n i) v)
    (huv : u ≠ v) (hnon : u ≠ -v) :
    ∃ w : Metric.sphere (0 : Pt) 1, ∀ i, h i < inner ℝ (n i) (w : Pt) := by
  have hsum0 : u + v ≠ 0 := by
    intro hh
    apply hnon
    exact eq_neg_of_add_eq_zero_left hh
  have hs0 : 0 < ‖u + v‖ := norm_pos_iff.mpr hsum0
  have hdist : 0 < ‖u - v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr huv))
  have hs2 : ‖u + v‖ ^ 2 < 4 := by
    have hh := parallelogram_law_with_norm ℝ u v
    rw [hus, hvs] at hh
    nlinarith
  have hs : ‖u + v‖ < 2 := by nlinarith [norm_nonneg (u + v)]
  let w : Pt := ‖u + v‖⁻¹ • (u + v)
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0), inv_mul_cancel₀ hs0.ne']
  refine ⟨⟨w, by simpa [Metric.mem_sphere, dist_eq_norm] using hw⟩, ?_⟩
  intro i
  change h i < inner ℝ (n i) w
  dsimp [w]
  rw [inner_smul_right, inner_add_right]
  have hi : 2 * h i ≤ inner ℝ (n i) u + inner ℝ (n i) v := by linarith [hu i, hv i]
  have hz : h i * ‖u + v‖ < inner ℝ (n i) u + inner ℝ (n i) v := by nlinarith [hpos i]
  rw [inv_mul_eq_div]
  exact (lt_div_iff₀ hs0).mpr hz

