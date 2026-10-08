import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_active_cap_not_interior (n u : Pt) (h : ℝ)
    (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) (h0 : 0 ≤ h) (h1 : h < 1) (heq : inner ℝ n u = h) :
    u ∉ sInterior (cap n h) := by
  let w := h • u - n
  let v : ℝ → Pt := fun t => u + t • w
  have huw : inner ℝ u w = 0 := by simp [w, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, real_inner_comm, heq]
  have hnw : inner ℝ n w = h ^ 2 - 1 := by simp [w, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn, heq]; ring
  have hh : h ^ 2 < 1 := by nlinarith
  have hvnorm (t : ℝ) : 1 ≤ ‖v t‖ := by
    have hsq : ‖v t‖ ^ 2 = 1 + t ^ 2 * ‖w‖ ^ 2 := by
      dsimp only [v]
      rw [norm_add_sq_real, hu, norm_smul, real_inner_smul_right, huw]
      simp [Real.norm_eq_abs, mul_pow]
    nlinarith [norm_nonneg (v t), sq_nonneg t, sq_nonneg ‖w‖, mul_nonneg (sq_nonneg t) (sq_nonneg ‖w‖)]
  let fs : ℝ → Metric.sphere (0 : Pt) 1 := fun t =>
    ⟨‖v t‖⁻¹ • v t, by
      have hvp : 0 < ‖v t‖ := lt_of_lt_of_le zero_lt_one (hvnorm t)
      simpa [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp), ne_of_gt hvp]⟩
  have hfs : Continuous fs := by
    apply Continuous.subtype_mk
    have hv : Continuous v := continuous_const.add (continuous_id.smul continuous_const)
    exact (hv.norm.inv₀ (fun t => ne_of_gt (lt_of_lt_of_le zero_lt_one (hvnorm t)))).smul hv
  have hf0 : (fs 0 : Pt) = u := by simp [fs, v, hu]
  have hnot (t : ℝ) (ht : 0 < t) : fs t ∉ (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' cap n h := by
    intro hmem
    have hineq : h ≤ inner ℝ n (‖v t‖⁻¹ • v t) := hmem.2
    have hvp : 0 < ‖v t‖ := lt_of_lt_of_le zero_lt_one (hvnorm t)
    rw [real_inner_smul_right, show inner ℝ n (v t) = h + t * (h ^ 2 - 1) by simp [v, inner_add_right, real_inner_smul_right, heq, hnw], ← div_eq_inv_mul] at hineq
    have hmul := (le_div_iff₀ hvp).mp hineq
    have hge : h ≤ h * ‖v t‖ := by nlinarith [hvnorm t]
    nlinarith [mul_neg_of_pos_of_neg ht (sub_neg.mpr hh)]
  have hzero : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact Set.mem_Ici.mpr le_rfl
  have hcl : fs 0 ∈ closure (fs '' Set.Ioi (0 : ℝ)) := mem_closure_image hfs.continuousAt hzero
  have hsubset : fs '' Set.Ioi (0 : ℝ) ⊆ ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' cap n h)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    exact hnot t ht
  have hbad := closure_mono hsubset hcl
  rintro ⟨us, hus, he⟩
  have hus0 : us = fs 0 := by apply Subtype.ext; simpa [hf0] using he
  rw [hus0] at hus
  rw [closure_compl] at hbad
  exact hbad hus
