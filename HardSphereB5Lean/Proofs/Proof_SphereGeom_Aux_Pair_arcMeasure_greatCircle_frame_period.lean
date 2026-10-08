import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_restrict_circle
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_circle_image
set_option autoImplicit false
open MeasureTheory SphereGeom
theorem proof_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame_period (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁, v₂, p]) :
    arcMeasure.restrict (greatCircle p) =
      (volume.restrict (Set.Ico 0 (2 * Real.pi))).map (circlePt 0 v₁ v₂ 1) := by
  have hp : Function.Periodic (circlePt 0 v₁ v₂ 1) (2 * Real.pi) := by
    intro t; simp [circlePt, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have himage : circlePt 0 v₁ v₂ 1 '' Set.Icc 0 (2 * Real.pi) = greatCircle p := by
    rw [show (2 * Real.pi) = 0 + 2 * Real.pi by ring, hp.image_Icc (by positivity)]
    rw [← hp.image_Icc (by positivity) (-Real.pi)]
    convert SphereGeom.Aux.Pair.circle_image v₁ v₂ p hv using 2 <;> ring
  have he : Orthonormal ℝ ![v₁, v₂] := by
    apply orthonormal_iff_ite.mpr
    intro i j
    have h := orthonormal_iff_ite.mp hv (Fin.castAdd 1 i) (Fin.castAdd 1 j)
    fin_cases i <;> fin_cases j <;> simpa using h
  have hm := arcMeasure_restrict_circle (0 : E3) ![v₁, v₂] he 1 (by norm_num)
    0 (2 * Real.pi) (by positivity) (by linarith)
  simpa [himage, restrict_Ico_eq_restrict_Icc] using hm
