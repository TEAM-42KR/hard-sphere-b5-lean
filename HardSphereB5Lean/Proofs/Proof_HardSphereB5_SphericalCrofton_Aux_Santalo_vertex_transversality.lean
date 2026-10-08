import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_sigma_gram_data
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_cross_identities
set_option autoImplicit false
noncomputable section
open SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

private lemma tangent_cross_triple (x y w : Pt) :
    inner ℝ w (cross (cross x w) (cross y w)) =
      inner ℝ (cross x y) w * inner ℝ w w := by
  have hi (p q : Pt) : inner ℝ p q = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]; ring
  simp_rw [hi]
  simp only [SphereGeom.cross, WithLp.ofLp_toLp, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_vertex_transversality (D w : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) (hw : w ∈ vertsD D) :
    cross (cross (nAv D) w) (cross (nBv D) w) ≠ 0 := by
  rcases HardSphereB5.SphericalCrofton.Aux.Geom.sigma_gram_data D hD hoff with
    ⟨hx, hy, hk, ha, hb, hab, hba, hR2, hR0, hSigma, hverts⟩
  rw [hverts] at hw
  rcases hw with ⟨hw, hAw, hBw⟩
  let c := inner ℝ (nAv D) (nBv D)
  let k := 1 - c ^ 2
  let a := ‖D‖ / 2
  let b := ‖D - e‖ / 2
  let N := a ^ 2 - 2 * c * a * b + b ^ 2
  let d := inner ℝ (cross (nAv D) (nBv D)) w
  have hself : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hxself : inner ℝ (nAv D) (nAv D) = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyself : inner ℝ (nBv D) (nBv D) = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hproject := (HardSphereB5.SphericalCrofton.Aux.Geom.cross_identities (nAv D) (nBv D) w).2.2.2
  have hscalar := congrArg (fun z : Pt => inner ℝ z w) hproject
  simp only [inner_add_left, real_inner_smul_left, hxself, hyself, hself, hAw, hBw] at hscalar
  have hdelta : d ^ 2 = k - N := by dsimp [d, k, N, a, b, c]; nlinarith [hscalar]
  have hN : N < k := by
    have hRsq : Rc ‖D‖ ‖D - e‖ ^ 2 < 1 := by nlinarith [hR0, hR]
    have hdiv : N / k < 1 := by simpa [N, k, a, b, c] using hR2.trans_lt hRsq
    exact (div_lt_one hk).mp hdiv
  have hd : d ≠ 0 := by nlinarith [hdelta, hN]
  intro hzero
  have ht := tangent_cross_triple (nAv D) (nBv D) w
  rw [hzero, inner_zero_right, hself, mul_one] at ht
  exact hd ht.symm
