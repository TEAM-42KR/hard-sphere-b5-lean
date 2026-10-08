import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_gram_projection
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_strict_cap_interior
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_gram_interior (x y : Pt) (a b c : ℝ)
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
