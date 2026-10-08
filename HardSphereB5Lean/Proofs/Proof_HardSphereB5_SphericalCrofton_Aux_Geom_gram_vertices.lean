import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_cross_identities
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 2000000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_gram_vertices (x y : Pt) (a b c : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = c)
    (hd : 0 < 1 - c ^ 2)
    (hq : (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) < 1) :
    ∃ V W : Pt, V ≠ W ∧ {u : Pt | ‖u‖ = 1 ∧ inner ℝ x u = a ∧ inner ℝ y u = b} = {V, W} := by
  let d := 1 - c ^ 2
  let q := (a ^ 2 - 2 * c * a * b + b ^ 2) / d
  let α := (a - c * b) / d
  let β := (b - c * a) / d
  let p : Pt := α • x + β • y
  let z := cross x y
  let r := √((1 - q) / d)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyy : inner ℝ y y = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hyx : inner ℝ y x = c := by rw [real_inner_comm, hxy]
  have hz := Aux.Geom.cross_identities x y p
  have hxz : inner ℝ x z = 0 := hz.1
  have hyz : inner ℝ y z = 0 := hz.2.1
  have hzz : inner ℝ z z = d := by simpa only [z, hxx, hyy, hxy, one_mul, d] using hz.2.2.1
  have hpx : inner ℝ x p = a := by
    dsimp [p]
    rw [inner_add_right, inner_smul_right, inner_smul_right, hxx, hxy]
    dsimp [α, β]
    field_simp
    <;> dsimp [d] at *
    <;> nlinarith [ne_of_gt hd]
  have hpy : inner ℝ y p = b := by
    dsimp [p]
    rw [inner_add_right, inner_smul_right, inner_smul_right, hyx, hyy]
    dsimp [α, β]
    field_simp
    <;> dsimp [d] at *
    <;> nlinarith [ne_of_gt hd]
  have hpp : inner ℝ p p = q := by
    change inner ℝ (α • x + β • y) p = q
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hpx, hpy]
    dsimp [α, β, q]
    field_simp
    <;> dsimp [d] at *
    <;> nlinarith [ne_of_gt hd]
  have hpz : inner ℝ p z = 0 := by simp [p, inner_add_left, real_inner_smul_left, hxz, hyz]
  have hzp : inner ℝ z p = 0 := by rw [real_inner_comm, hpz]
  have hr2 : r ^ 2 = (1 - q) / d := Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hq.le) hd.le)
  have hrd : r ^ 2 * d = 1 - q := by rw [hr2]; exact div_mul_cancel₀ _ hd0
  have hr : 0 < r := Real.sqrt_pos.2 (div_pos (sub_pos.mpr hq) hd)
  have hpadd (t : ℝ) : ‖p + t • z‖ ^ 2 = q + t ^ 2 * d := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hpp, hpz, hzp, hzz]
    ring
  have hmem (t : ℝ) (ht : t ^ 2 = r ^ 2) :
      ‖p + t • z‖ = 1 ∧ inner ℝ x (p + t • z) = a ∧ inner ℝ y (p + t • z) = b := by
    refine ⟨?_, ?_, ?_⟩
    · have hnorm := hpadd t
      rw [ht] at hnorm
      nlinarith [norm_nonneg (p + t • z)]
    · simp [inner_add_right, inner_smul_right, hpx, hxz]
    · simp [inner_add_right, inner_smul_right, hpy, hyz]
  refine ⟨p + r • z, p + (-r) • z, ?_, ?_⟩
  · intro heq
    have hi := congrArg (fun u : Pt => inner ℝ z u) heq
    simp only [inner_add_right, real_inner_smul_right, hzp, hzz, zero_add] at hi
    nlinarith
  · ext u
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu, hux, huy⟩
      let t := inner ℝ z u / d
      have hid := (Aux.Geom.cross_identities x y u).2.2.2
      rw [hxx, hyy, hxy, hux, huy] at hid
      have hup : u = p + t • z := by
        calc u = d⁻¹ • (d • u) := by simp [smul_smul, hd0]
             _ = p + t • z := by
               rw [show d • u = (a - c * b) • x + (b - c * a) • y + inner ℝ z u • z by simpa [d, z] using hid]
               simp [p, α, β, t, smul_add, smul_smul, div_eq_mul_inv, mul_comm]
      have hnorm := hpadd t
      rw [← hup, hu] at hnorm
      have ht2 : t ^ 2 = r ^ 2 := by nlinarith
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp ht2 with ht | ht
      · left; simpa [ht] using hup
      · right; simpa [ht] using hup
    · rintro (rfl | rfl)
      · exact hmem r rfl
      · exact hmem (-r) (by ring)
