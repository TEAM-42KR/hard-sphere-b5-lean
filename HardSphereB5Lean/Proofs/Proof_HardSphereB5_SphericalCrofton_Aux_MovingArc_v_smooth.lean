import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_unitDir_smooth
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
set_option maxHeartbeats 800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_v_smooth (D : Pt) (t : ℝ) (hD : D ≠ e) (hr : ‖D-e‖ < 2) (hB : rawB D ≠ 0) :
    ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => v x.1 x.2) (D,t) := by
  have hsub : D-e ≠ 0 := sub_ne_zero.mpr hD
  have hDn : ‖D-e‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
  have hDE : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => x.1-e) (D,t) :=
    contDiffAt_fst.sub contDiffAt_const
  have hnB : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => nBv x.1) (D,t) := by
    dsimp only [nBv]
    exact ((hDE.norm ℝ hsub).inv hDn).smul
      (contDiffAt_const.sub contDiffAt_fst)
  have hraw : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => rawB x.1) (D,t) := by
    dsimp only [rawB]
    exact contDiffAt_const.sub ((hnB.inner ℝ contDiffAt_const).smul hnB)
  have hEB : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => unitDir (rawB x.1)) (D,t) :=
    ContDiffAt.comp (g := unitDir) (f := fun x : Pt × ℝ => rawB x.1) (D,t)
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.unitDir_smooth (rawB D) hB) hraw
  have hcross : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => cross (nBv x.1) (unitDir (rawB x.1))) (D,t) := by
    unfold cross
    apply PiLp.contDiff_toLp.contDiffAt.comp
    apply contDiffAt_pi.2
    have h1 (i : Fin 3) : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => nBv x.1 i) (D,t) :=
      (contDiffAt_piLp 2).mp hnB i
    have h2 (i : Fin 3) : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => unitDir (rawB x.1) i) (D,t) :=
      (contDiffAt_piLp 2).mp hEB i
    intro i
    fin_cases i
    · change ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => nBv x.1 1 * unitDir (rawB x.1) 2 - nBv x.1 2 * unitDir (rawB x.1) 1) (D,t)
      exact ((h1 1).mul (h2 2)).sub ((h1 2).mul (h2 1))
    · change ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => nBv x.1 2 * unitDir (rawB x.1) 0 - nBv x.1 0 * unitDir (rawB x.1) 2) (D,t)
      exact ((h1 2).mul (h2 0)).sub ((h1 0).mul (h2 2))
    · change ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => nBv x.1 0 * unitDir (rawB x.1) 1 - nBv x.1 1 * unitDir (rawB x.1) 0) (D,t)
      exact ((h1 0).mul (h2 1)).sub ((h1 1).mul (h2 0))
  have hrad : 1 - ‖D-e‖^2 / 4 ≠ 0 := by
    have hp : 0 ≤ ‖D-e‖ := norm_nonneg (D-e)
    nlinarith
  have hrB : ContDiffAt ℝ ⊤ (fun x : Pt × ℝ => rB x.1) (D,t) := by
    unfold rB
    exact (contDiffAt_const.sub ((hDE.norm_sq ℝ).div_const 4)).sqrt hrad
  change ContDiffAt ℝ ⊤ (fun x : Pt × ℝ =>
    (1/2 : ℝ) • (e-x.1) + rB x.1 •
      (Real.cos x.2 • unitDir (rawB x.1) + Real.sin x.2 • -cross (nBv x.1) (unitDir (rawB x.1)))) (D,t)
  exact ((contDiffAt_const.sub contDiffAt_fst).const_smul (1/2 : ℝ)).add
    (hrB.smul ((contDiffAt_snd.cos.smul hEB).add (contDiffAt_snd.sin.smul hcross.neg)))
