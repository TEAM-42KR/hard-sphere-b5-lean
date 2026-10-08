import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

set_option backward.isDefEq.respectTransparency false in
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_regular_of_triple (D u v : Pt) (hT : inner ℝ (cross u v) e ≠ 0) :
    centerFrame0 (v-u) ≠ 0 ∧ centerPhase D (D+u) (D+v) ∈ Complex.slitPlane := by
  have htr (x y z : Pt) : inner ℝ (cross x y) z =
      z 0 * (x 1 * y 2 - x 2 * y 1) + z 1 * (x 2 * y 0 - x 0 * y 2) +
        z 2 * (x 0 * y 1 - x 1 * y 0) := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
    rfl
  have hw0 : v-u ≠ 0 := by
    intro hw
    have hv : v = u := sub_eq_zero.mp hw
    apply hT
    subst v
    simp [cross, cross_self]
  have hwn : ‖v-u‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  let w := v-u
  let R := e - (inner ℝ (unitDir w) e) • unitDir w
  have hwperp : inner ℝ (cross u v) w = 0 := by
    dsimp [w]
    simp only [inner_sub_right]
    have h1 : inner ℝ (cross u v) v = 0 := by rw [htr]; ring
    have h2 : inner ℝ (cross u v) u = 0 := by rw [htr]; ring
    rw [h1, h2, sub_self]
  have hR0 : R ≠ 0 := by
    intro hz
    have he : e = (inner ℝ (unitDir w) e) • unitDir w := sub_eq_zero.mp hz
    apply hT
    rw [he, real_inner_smul_right]
    simp only [unitDir, real_inner_smul_right, hwperp, mul_zero]
  have hRn : ‖R‖ ≠ 0 := norm_ne_zero_iff.mpr hR0
  have hf : centerFrame0 (v-u) ≠ 0 := by
    change ‖R‖⁻¹ • R ≠ 0
    exact smul_ne_zero (inv_ne_zero hRn) hR0
  have him : (centerPhase D (D+u) (D+v)).im =
      -(‖w‖⁻¹ * ‖R‖⁻¹ * inner ℝ (cross u v) e) := by
    unfold centerPhase centerFrame1 centerFrame0
    have hd : D+v-(D+u) = w := by dsimp [w]; abel
    rw [hd]
    change inner ℝ (cross (‖w‖⁻¹ • w) (‖R‖⁻¹ • R))
      (D - midpoint ℝ (D+u) (D+v)) = _
    have hm : D - midpoint ℝ (D+u) (D+v) = (-1/2 : ℝ) • (u+v) := by
      simp only [midpoint_eq_smul_add, invOf_eq_inv, smul_add, smul_smul]
      norm_num
      module
    rw [hm]
    have halg (m n k : ℝ) : inner ℝ (cross (m • w) (n • (e-k • w)))
        ((-1/2 : ℝ) • (u+v)) = -(m*n*inner ℝ (cross u v) e) := by
      dsimp only [w]
      simp only [htr, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    simpa only [R, unitDir, smul_smul] using halg ‖w‖⁻¹ ‖R‖⁻¹
      (inner ℝ (unitDir w) e * ‖w‖⁻¹)
  have him0 : (centerPhase D (D+u) (D+v)).im ≠ 0 := by
    rw [him]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (inv_ne_zero hwn) (inv_ne_zero hRn)) hT)
  exact ⟨hf, Complex.mem_slitPlane_iff.mpr (Or.inr him0)⟩
