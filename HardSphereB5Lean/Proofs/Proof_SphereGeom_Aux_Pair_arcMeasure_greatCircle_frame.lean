import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_restrict_circle
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_circle_image
set_option autoImplicit false
open MeasureTheory SphereGeom
theorem proof_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁, v₂, p]) :
    arcMeasure.restrict (greatCircle p) =
      (volume.restrict (Set.Icc (-Real.pi) Real.pi)).map (circlePt 0 v₁ v₂ 1) := by
  have he : Orthonormal ℝ ![v₁, v₂] := by
    apply orthonormal_iff_ite.mpr
    intro i j
    have h := orthonormal_iff_ite.mp hv (Fin.castAdd 1 i) (Fin.castAdd 1 j)
    fin_cases i <;> fin_cases j <;> simpa using h
  have hm := arcMeasure_restrict_circle (0 : E3) ![v₁, v₂] he 1 (by norm_num)
    (-Real.pi) Real.pi (by linarith [Real.pi_pos]) (by linarith)
  simpa [SphereGeom.Aux.Pair.circle_image v₁ v₂ p hv] using hm
