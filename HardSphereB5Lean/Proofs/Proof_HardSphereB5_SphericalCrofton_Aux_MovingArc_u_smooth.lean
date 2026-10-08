import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_unitDir_smooth
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
set_option maxHeartbeats 800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_u_smooth (D : Pt) (t : ℝ) (hD : D ≠ 0) (hr : ‖D‖ < 2) (hA : rawA D ≠ 0) :
    ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => u x.1 x.2) (D,t) := by
  have hDn : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  have hnA : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => nAv x.1) (D,t) := by
    dsimp only [nAv]
    exact ((contDiffAt_fst.norm ℝ hD).inv hDn).smul contDiffAt_fst.neg
  have hraw : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => rawA x.1) (D,t) := by
    dsimp only [rawA]
    exact contDiffAt_const.sub ((hnA.inner ℝ contDiffAt_const).smul hnA)
  have hEA : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => unitDir (rawA x.1)) (D,t) :=
    ContDiffAt.comp (g := unitDir) (f := fun x : Pt × ℝ => rawA x.1) (D,t)
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.unitDir_smooth (rawA D) hA) hraw
  have hcross : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => cross (nAv x.1) (unitDir (rawA x.1))) (D,t) := by
    unfold cross
    apply PiLp.contDiff_toLp.contDiffAt.comp
    apply contDiffAt_pi.2
    have h1 (i : Fin 3) : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => nAv x.1 i) (D,t) :=
      (contDiffAt_piLp 2).mp hnA i
    have h2 (i : Fin 3) : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => unitDir (rawA x.1) i) (D,t) :=
      (contDiffAt_piLp 2).mp hEA i
    intro i
    fin_cases i
    · change ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => nAv x.1 1 * unitDir (rawA x.1) 2 - nAv x.1 2 * unitDir (rawA x.1) 1) (D,t)
      exact ((h1 1).mul (h2 2)).sub ((h1 2).mul (h2 1))
    · change ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => nAv x.1 2 * unitDir (rawA x.1) 0 - nAv x.1 0 * unitDir (rawA x.1) 2) (D,t)
      exact ((h1 2).mul (h2 0)).sub ((h1 0).mul (h2 2))
    · change ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => nAv x.1 0 * unitDir (rawA x.1) 1 - nAv x.1 1 * unitDir (rawA x.1) 0) (D,t)
      exact ((h1 0).mul (h2 1)).sub ((h1 1).mul (h2 0))
  have hrad : 1 - ‖D‖^2 / 4 ≠ 0 := by
    have hp : 0 ≤ ‖D‖ := norm_nonneg D
    nlinarith
  have hrA : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => rA x.1) (D,t) := by
    unfold rA
    exact (contDiffAt_const.sub ((contDiffAt_fst.norm_sq ℝ).div_const 4)).sqrt hrad
  change ContDiffAt ℝ ⊤ (fun x : Pt × ℝ =>
    (-1/2 : ℝ) • x.1 + rA x.1 •
      (Real.cos x.2 • unitDir (rawA x.1) + Real.sin x.2 • cross (nAv x.1) (unitDir (rawA x.1)))) (D,t)
  exact (contDiffAt_fst.const_smul (-1/2 : ℝ)).add
    (hrA.smul ((contDiffAt_snd.cos.smul hEA).add (contDiffAt_snd.sin.smul hcross)))
