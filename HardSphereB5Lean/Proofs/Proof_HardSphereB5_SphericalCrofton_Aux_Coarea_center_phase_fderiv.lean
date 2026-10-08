import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_phase_fderiv
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_phase_fderiv (D p p' : Pt) (hz : centerPhase D p p' ∈ Complex.slitPlane) :
    HasFDerivAt (fun W : Pt => Complex.arg (centerPhase W p p'))
      ((inner ℝ (centerFrame0 (p'-p)) (D-midpoint ℝ p p') /
          ((inner ℝ (centerFrame0 (p'-p)) (D-midpoint ℝ p p'))^2 +
            (inner ℝ (centerFrame1 (p'-p)) (D-midpoint ℝ p p'))^2)) •
        (innerSL ℝ (centerFrame1 (p'-p))) -
      (inner ℝ (centerFrame1 (p'-p)) (D-midpoint ℝ p p') /
          ((inner ℝ (centerFrame0 (p'-p)) (D-midpoint ℝ p p'))^2 +
            (inner ℝ (centerFrame1 (p'-p)) (D-midpoint ℝ p p'))^2)) •
        (innerSL ℝ (centerFrame0 (p'-p)))) D  := by
  let m := midpoint ℝ p p'
  let L0 : Pt →L[ℝ] ℝ := innerSL ℝ (centerFrame0 (p'-p))
  let L1 : Pt →L[ℝ] ℝ := innerSL ℝ (centerFrame1 (p'-p))
  let A := L0 (D-m)
  let B := L1 (D-m)
  let K : Pt →L[ℝ] (ℝ × ℝ) := L0.prod L1
  have hP : HasFDerivAt (fun W : Pt => (L0 (W-m), L1 (W-m))) K D := by
    simpa only [map_sub] using ((L0.hasFDerivAt.sub_const (L0 m)).prodMk
      (L1.hasFDerivAt.sub_const (L1 m)))
  have hphase := HardSphereB5.SphericalCrofton.Aux.Coarea.phase_fderiv A B hz
  have hc := hphase.comp D hP
  have hK : ((A/(A^2+B^2)) • ContinuousLinearMap.snd ℝ ℝ ℝ -
      (B/(A^2+B^2)) • ContinuousLinearMap.fst ℝ ℝ ℝ).comp K =
      (A/(A^2+B^2)) • L1 - (B/(A^2+B^2)) • L0 := by
    apply ContinuousLinearMap.ext
    intro W
    rfl
  rw [hK] at hc
  exact hc
