import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_trig_zeros_finite
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_endpoint_coord_two_zeros_finite (D : Pt) (hD2 : D 2 ≠ 0) :
    {α ∈ Set.Icc (-Real.pi) Real.pi | (D + u D α) 2 = 0}.Finite ∧
    {β ∈ Set.Icc (-Real.pi) Real.pi | (D + v D β) 2 = 0}.Finite := by
  have hconst : -(D 2 / 2) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hD2 (by norm_num))
  constructor
  · have hf := SphereGeom.Aux.Arrangement.trig_zeros_finite
      (rA D * (EA D 0) 2) (rA D * (EA D 1) 2) (-(D 2 / 2))
      (-Real.pi) Real.pi (Or.inr (Or.inr hconst))
    apply hf.subset
    intro α hα
    refine ⟨hα.1, ?_⟩
    have hform : rA D * (EA D 0) 2 * Real.cos α + rA D * (EA D 1) 2 * Real.sin α - (-(D 2 / 2)) =
        (D + u D α) 2 := by
      simp only [u, circlePt, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hform]; exact hα.2
  · have hf := SphereGeom.Aux.Arrangement.trig_zeros_finite
      (rB D * (EB D 0) 2) (rB D * (EB D 1) 2) (-(D 2 / 2))
      (-Real.pi) Real.pi (Or.inr (Or.inr hconst))
    apply hf.subset
    intro β hβ
    refine ⟨hβ.1, ?_⟩
    have hform : rB D * (EB D 0) 2 * Real.cos β + rB D * (EB D 1) 2 * Real.sin β - (-(D 2 / 2)) =
        (D + v D β) 2 := by
      simp only [v, circlePt, HardSphereB5.SphericalCrofton.Aux.MovingArc.cB,
        PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      have he2 : e 2 = 0 := by simp [e]
      rw [he2]
      ring
    rw [hform]; exact hβ.2
