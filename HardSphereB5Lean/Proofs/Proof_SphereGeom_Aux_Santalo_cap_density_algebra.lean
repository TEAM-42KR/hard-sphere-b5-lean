import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_cross_norm_sq
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open scoped Classical

theorem proof_SphereGeom_Aux_Santalo_cap_density_algebra
    (nA nB u v : E3) (a b : ℝ)
    (hnA : ‖nA‖ = 1) (hnB : ‖nB‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hAu : inner ℝ nA u = a) (hBv : inner ℝ nB v = b)
    (hAv : a ≤ inner ℝ nA v) (hBu : b ≤ inner ℝ nB u)
    (hx0 : -1 < inner ℝ u v) (hx1 : inner ℝ u v < 1) :
    ‖cross nA u‖ = Real.sqrt (1 - a ^ 2) ∧
    ‖cross nB v‖ = Real.sqrt (1 - b ^ 2) ∧
    0 ≤ inner ℝ nA v - a * inner ℝ u v ∧
    0 ≤ inner ℝ nB u - b * inner ℝ u v ∧
    Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) *
      santaloDens u v (unitDir (cross nA u)) (unitDir (cross nB v)) =
      (inner ℝ nA v - a * inner ℝ u v) *
        (inner ℝ nB u - b * inner ℝ u v) /
          Real.sin (Real.arccos (inner ℝ u v)) ^ 3 := by
  have hcross (p q r s : E3) :
      inner ℝ (cross p q) (cross r s) =
        inner ℝ p r * inner ℝ q s - inner ℝ p s * inner ℝ q r := by
    have hinner (z w : E3) : inner ℝ z w =
        z 0 * w 0 + z 1 * w 1 + z 2 * w 2 := by
      simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]
      <;> ring
    simp_rw [hinner]
    simp only [SphereGeom.cross, WithLp.ofLp_toLp, cross_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    ring
  have hsqA : ‖cross nA u‖ ^ 2 = 1 - a ^ 2 := by
    simpa [hnA, hu, hAu] using SphereGeom.Aux.Santalo.cross_norm_sq nA u
  have hsqB : ‖cross nB v‖ ^ 2 = 1 - b ^ 2 := by
    simpa [hnB, hv, hBv] using SphereGeom.Aux.Santalo.cross_norm_sq nB v
  have hsA : ‖cross nA u‖ = Real.sqrt (1 - a ^ 2) := by
    rw [← hsqA, Real.sqrt_sq (norm_nonneg _)]
  have hsB : ‖cross nB v‖ = Real.sqrt (1 - b ^ 2) := by
    rw [← hsqB, Real.sqrt_sq (norm_nonneg _)]
  have hrA : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hrB : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hfA : 0 ≤ inner ℝ nA v - a * inner ℝ u v := by
    have hmul : a * inner ℝ u v ≤ a := mul_le_of_le_one_right ha0.le hx1.le
    linarith
  have hfB : 0 ≤ inner ℝ nB u - b * inner ℝ u v := by
    have hmul : b * inner ℝ u v ≤ b := mul_le_of_le_one_right hb0.le hx1.le
    linarith
  have hca : inner ℝ (cross u v) (cross nA u) =
      -(inner ℝ nA v - a * inner ℝ u v) := by
    rw [hcross, real_inner_comm nA u, hAu, real_inner_self_eq_norm_sq,
      hu, real_inner_comm nA v, real_inner_comm u v]
    ring
  have hcb : inner ℝ (cross u v) (cross nB v) =
      inner ℝ nB u - b * inner ℝ u v := by
    rw [hcross, real_inner_comm nB u, real_inner_self_eq_norm_sq, hv,
      real_inner_comm nB v, hBv]
    ring
  have hnormA : |inner ℝ (cross u v) (unitDir (cross nA u))| =
      (Real.sqrt (1 - a ^ 2))⁻¹ * (inner ℝ nA v - a * inner ℝ u v) := by
    rw [unitDir, real_inner_smul_right, hsA, hca, abs_mul,
      abs_of_pos (inv_pos.mpr hrA), abs_neg, abs_of_nonneg hfA]
  have hnormB : |inner ℝ (cross u v) (unitDir (cross nB v))| =
      (Real.sqrt (1 - b ^ 2))⁻¹ * (inner ℝ nB u - b * inner ℝ u v) := by
    rw [unitDir, real_inner_smul_right, hsB, hcb, abs_mul,
      abs_of_pos (inv_pos.mpr hrB), abs_of_nonneg hfB]
  refine ⟨hsA, hsB, hfA, hfB, ?_⟩
  unfold santaloDens
  rw [hnormA, hnormB]
  have hproduct : Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) *
      ((Real.sqrt (1 - a ^ 2))⁻¹ * (inner ℝ nA v - a * inner ℝ u v) *
        ((Real.sqrt (1 - b ^ 2))⁻¹ * (inner ℝ nB u - b * inner ℝ u v))) =
      (inner ℝ nA v - a * inner ℝ u v) *
        (inner ℝ nB u - b * inner ℝ u v) := by
    field_simp [ne_of_gt hrA, ne_of_gt hrB]
    <;> ring
  rw [← mul_div_assoc, hproduct]
