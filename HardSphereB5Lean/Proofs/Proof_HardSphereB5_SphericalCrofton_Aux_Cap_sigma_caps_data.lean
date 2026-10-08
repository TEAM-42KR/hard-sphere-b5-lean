import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_TwoBalls_ball_iff_inner
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Cap_sigma_caps_data (D : Pt) (hD0 : D ≠ 0) (hDe : D ≠ e) :
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

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_Cap_sigma_caps_data
