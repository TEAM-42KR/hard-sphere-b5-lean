import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_gram_projection (x y : Pt) (a b c : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = c) (hd : 0 < 1 - c ^ 2) :
    let p := ((a - c * b) / (1 - c ^ 2)) • x + ((b - c * a) / (1 - c ^ 2)) • y
    inner ℝ x p = a ∧ inner ℝ y p = b ∧
    ‖p‖ ^ 2 = (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) := by
  dsimp only
  let q := (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2)
  let α := (a - c * b) / (1 - c ^ 2)
  let β := (b - c * a) / (1 - c ^ 2)
  let p : Pt := α • x + β • y
  have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyy : inner ℝ y y = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hyx : inner ℝ y x = c := by rw [real_inner_comm, hxy]
  have hpx : inner ℝ x p = a := by
    dsimp [p]
    rw [inner_add_right, inner_smul_right, inner_smul_right, hxx, hxy]
    dsimp [α, β]
    field_simp
    <;> nlinarith [ne_of_gt hd]
  have hpy : inner ℝ y p = b := by
    dsimp [p]
    rw [inner_add_right, inner_smul_right, inner_smul_right, hyx, hyy]
    dsimp [α, β]
    field_simp
    <;> nlinarith [ne_of_gt hd]
  have hpp : inner ℝ p p = q := by
    dsimp [p]
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    change α * inner ℝ x p + β * inner ℝ y p = q
    rw [hpx, hpy]
    dsimp [α, β, q]
    field_simp
    <;> nlinarith [ne_of_gt hd]
  exact ⟨hpx, hpy, by rw [← real_inner_self_eq_norm_sq]; exact hpp⟩
