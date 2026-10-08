import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_trig_zeros_finite
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_cross_u_cB_axis_ne_zero
set_option autoImplicit false

open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.MovingArc
open HardSphereB5.Lean (Pt e)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_beta_cross_axis_zeros_finite (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D)
    (hD1 : D 1 ≠ 0) (α : ℝ) (hα : Real.sin α ≠ 0) :
    {β ∈ Set.Icc (-Real.pi) Real.pi |
      inner ℝ (SphereGeom.cross (u D α) (v D β)) e = 0}.Finite := by
  let A : ℝ := rB D * inner ℝ (SphereGeom.cross (u D α) (EB D 0)) e
  let B : ℝ := rB D * inner ℝ (SphereGeom.cross (u D α) (EB D 1)) e
  let C : ℝ := inner ℝ (SphereGeom.cross (u D α) (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D)) e
  have hC : C ≠ 0 :=
    HardSphereB5.SphericalCrofton.Aux.Coarea.cross_u_cB_axis_ne_zero D hL hoff hD1 α hα
  have hform (β : ℝ) :
      A * Real.cos β + B * Real.sin β - (-C) =
        inner ℝ (SphereGeom.cross (u D α) (v D β)) e := by
    dsimp [A, B, C]
    simp [v, circlePt, SphereGeom.cross, cross_apply, PiLp.inner_apply,
      Fin.sum_univ_succ, e, Matrix.vecHead, Matrix.vecTail]
    ring
  have hf := SphereGeom.Aux.Arrangement.trig_zeros_finite
    A B (-C) (-Real.pi) Real.pi (Or.inr (Or.inr (neg_ne_zero.mpr hC)))
  apply hf.subset
  intro β hβ
  exact ⟨hβ.1, by rw [hform]; exact hβ.2⟩
