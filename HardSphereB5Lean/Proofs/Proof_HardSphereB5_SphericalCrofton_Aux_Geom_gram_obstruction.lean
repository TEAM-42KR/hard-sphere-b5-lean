import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_gram_obstruction (x y : Pt) (a b c : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = c)
    (hd : 0 < 1 - c ^ 2) (ha : 0 ≤ a - c * b) (hb : 0 ≤ b - c * a) :
    let q := (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2)
    let p := ((a - c * b) / (1 - c ^ 2)) • x + ((b - c * a) / (1 - c ^ 2)) • y
    let K := {u : Pt | ‖u‖ = 1 ∧ a ≤ inner ℝ x u ∧ b ≤ inner ℝ y u}
    (K.Nonempty → q ≤ 1) ∧ (q = 1 → K = {p}) ∧ (1 < q → K = ∅) := by
  dsimp only
  let q := (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2)
  let α := (a - c * b) / (1 - c ^ 2)
  let β := (b - c * a) / (1 - c ^ 2)
  let p : Pt := α • x + β • y
  let K := {u : Pt | ‖u‖ = 1 ∧ a ≤ inner ℝ x u ∧ b ≤ inner ℝ y u}
  change (K.Nonempty → q ≤ 1) ∧ (q = 1 → K = {p}) ∧ (1 < q → K = ∅)
  have hα : 0 ≤ α := div_nonneg ha hd.le
  have hβ : 0 ≤ β := div_nonneg hb hd.le
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
  have hbound : ∀ u ∈ K, q ≤ 1 ∧ (q = 1 → u = p) := by
    intro u hu
    have hpu : q ≤ inner ℝ p u := by
      have hpq : α * a + β * b = q := by
        rw [← hpp]
        change α * a + β * b = inner ℝ (α • x + β • y) p
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hpx, hpy]
      dsimp [p]
      rw [inner_add_left, inner_smul_left, inner_smul_left, ← hpq]
      exact add_le_add (mul_le_mul_of_nonneg_left hu.2.1 hα) (mul_le_mul_of_nonneg_left hu.2.2 hβ)
    have hnorm : ‖u - p‖ ^ 2 = 1 + q - 2 * inner ℝ p u := by
      rw [norm_sub_sq_real, hu.1, ← real_inner_self_eq_norm_sq, hpp, real_inner_comm]
      ring
    have hz := sq_nonneg ‖u - p‖
    refine ⟨by nlinarith, ?_⟩
    intro hq
    have heq : ‖u - p‖ = 0 := by nlinarith [norm_nonneg (u - p)]
    exact sub_eq_zero.mp (norm_eq_zero.mp heq)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    exact (hbound u hu).1
  · intro hq
    ext u
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hu
      exact (hbound u hu).2 hq
    · rintro rfl
      refine ⟨?_, hpx.ge, hpy.ge⟩
      have hp1 : ‖p‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hpp, hq]
      nlinarith [norm_nonneg p]
  · intro hq
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact (not_le_of_gt hq) (hbound u hu).1
