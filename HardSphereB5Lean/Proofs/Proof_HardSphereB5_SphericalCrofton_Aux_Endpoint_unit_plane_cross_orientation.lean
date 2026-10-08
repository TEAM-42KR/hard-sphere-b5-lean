import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_cross_norm_sq
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pole_orientation
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_unit_plane_cross_orientation (u v p : Pt) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (hne : u ≠ v) (hanti : u ≠ -v) (hpu : inner ℝ p u = 0) (hpv : inner ℝ p v = 0) :
    cross u v ≠ 0 ∧ ((unitDir (cross u v) = p ∧ unitDir (cross v u) = -p) ∨
      (unitDir (cross u v) = -p ∧ unitDir (cross v u) = p)) := by
  have hzero (a b : Pt) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
      (hz : cross a b = 0) : a = b ∨ a = -b := by
    have hc := SphereGeom.Aux.Santalo.cross_norm_sq a b
    rw [ha, hb, hz, norm_zero] at hc
    have hi : inner ℝ a b = 1 ∨ inner ℝ a b = -1 := by
      have hs : (inner ℝ a b - 1) * (inner ℝ a b + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hs with hs | hs
      · left; linarith
      · right; linarith
    rcases hi with hi | hi
    · left
      have hh := norm_sub_sq_real a b
      rw [ha, hb, hi] at hh
      have hz : ‖a-b‖ = 0 := by nlinarith [norm_nonneg (a-b)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hz)
    · right
      have hh := norm_add_sq_real a b
      rw [ha, hb, hi] at hh
      have hz : ‖a+b‖ = 0 := by nlinarith [norm_nonneg (a+b)]
      exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp hz)
  have hc : cross u v ≠ 0 := by
    intro hz
    exact (hzero u v hu hv hz).elim hne hanti
  let z : Pt := unitDir (cross u v)
  have hz : ‖z‖ = 1 := (pole_orientation u v).2.2.2 hc
  have htriple : cross p (cross u v) = (inner ℝ p v) • u - (inner ℝ p u) • v := by
    ext i
    fin_cases i <;> simp [cross, cross_apply, PiLp.inner_apply, Fin.sum_univ_succ] <;> ring
  have hpz : cross p z = 0 := by
    have hs : cross p (unitDir (cross u v)) = ‖cross u v‖⁻¹ • cross p (cross u v) := by
      ext i
      fin_cases i <;> simp [cross, cross_apply, unitDir] <;> ring
    rw [hs, htriple, hpu, hpv]
    simp
  have hpm : z = p ∨ z = -p := by
    rcases hzero p z hp hz hpz with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h]; simp)
  have hswap : unitDir (cross v u) = -z := by
    have hh : cross v u = -cross u v := by
      ext i
      fin_cases i <;> simp [cross, cross_apply] <;> ring
    rw [hh]
    simp [unitDir, z]
  refine ⟨hc, ?_⟩
  rcases hpm with h | h
  · exact Or.inl ⟨h, by rw [hswap, h]⟩
  · exact Or.inr ⟨h, by rw [hswap, h, neg_neg]⟩
