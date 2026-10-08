import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_A
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
noncomputable section
private theorem cross_neg_native (a b : Pt) : cross (-a) (-b) = cross a b := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring
private theorem reflect_axis (D : Pt) : nAv (e-D)= -nBv D := by
  simp only [nAv, nBv, norm_sub_rev e D, smul_neg]

private theorem reflect_raw (D : Pt) : rawA (e-D)= -rawB D := by
  rw [rawA, reflect_axis, rawB]
  simp only [inner_neg_left, inner_neg_right, neg_smul, smul_neg]
  module

private theorem reflect_unit (D : Pt) : unitDir (rawA (e-D))= -unitDir (rawB D) := by
  rw [reflect_raw]
  simp [unitDir]

private theorem reflect_E0 (D : Pt) : EA (e-D) 0= -(EB D 0) := by
  simpa only [EA, EB, Matrix.cons_val_zero] using reflect_unit D

private theorem reflect_E1 (D : Pt) : EA (e-D) 1= -(EB D 1) := by
  change cross (nAv (e-D)) (unitDir (rawA (e-D)))=
    -(-cross (nBv D) (unitDir (rawB D)))
  rw [reflect_axis, reflect_unit, cross_neg_native, neg_neg]

private theorem reflect_center (D : Pt) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.cA (e-D)= -HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D := by
  simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, HardSphereB5.SphericalCrofton.Aux.MovingArc.cB]
  module

private theorem reflect_radius (D : Pt) : rA (e-D)=rB D := by
  simp only [rA, rB, norm_sub_rev e D]

private theorem reflect_chart (D : Pt) (t : ℝ) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) t= -HardSphereB5.SphericalCrofton.Aux.MovingArc.v D t := by
  simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, HardSphereB5.SphericalCrofton.Aux.MovingArc.v,
    circlePt, reflect_center, reflect_E0, reflect_E1, reflect_radius]
  module

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_B (D : Pt) (hoff : offAxis D) (hr : ‖D-e‖ < 2) (θ : ℝ) :
    ‖v D θ‖ = 1 ∧ ‖D+v D θ-e‖ = 1 := by
  have href : offAxis (e-D) := by
    intro t ht
    apply hoff (1-t)
    calc
      D = e-(e-D) := by abel
      _ = e-t•e := by rw [ht]
      _ = (1-t)•e := by module
  have hrad : ‖e-D‖ < 2 := by simpa only [norm_sub_rev e D] using hr
  have h := HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_A (e-D) href hrad θ
  rw [reflect_chart] at h
  have hh : (e-D)+(-v D θ) = -(D+v D θ-e) := by abel
  rw [hh, norm_neg, norm_neg] at h
  exact h
