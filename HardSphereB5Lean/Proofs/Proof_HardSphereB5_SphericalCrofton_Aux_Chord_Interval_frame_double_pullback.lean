import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame_period
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_frame_double_pullback (E1 E2 p : Pt) (hE : Orthonormal ℝ ![E1,E2,p])
    (H : Pt → Pt → ENNReal) (hH : Measurable (Function.uncurry H)) :
    (∫⁻ s in Set.Ioc 0 (2 * π), ∫⁻ t in Set.Ioc 0 (2 * π),
      H (circlePt 0 E1 E2 1 s) (circlePt 0 E1 E2 1 t)) =
    ∫⁻ u in greatCircle p, ∫⁻ v in greatCircle p, H u v ∂arcMeasure ∂arcMeasure := by
  let C : ℝ → Pt := circlePt 0 E1 E2 1
  have hC : Measurable C := by
    have hc : Continuous C := by unfold C circlePt; fun_prop
    exact hc.measurable
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * π))
  have hmap : arcMeasure.restrict (greatCircle p) = ν.map C := by
    simpa only [ν, C, restrict_Ico_eq_restrict_Icc, restrict_Ioc_eq_restrict_Icc]
      using SphereGeom.Aux.Pair.arcMeasure_greatCircle_frame_period E1 E2 p hE
  symm
  rw [hmap]
  change (∫⁻ u, ∫⁻ v, H u v ∂ν.map C ∂ν.map C) = _
  calc
    (∫⁻ u, ∫⁻ v, H u v ∂ν.map C ∂ν.map C) =
        ∫⁻ u, ∫⁻ t, H u (C t) ∂ν ∂ν.map C := by
      apply lintegral_congr
      intro u
      exact lintegral_map (hH.comp (measurable_const.prodMk measurable_id)) hC
    _ = ∫⁻ s, ∫⁻ t, H (C s) (C t) ∂ν ∂ν :=
      lintegral_map
        ((hH.comp (measurable_fst.prodMk (hC.comp measurable_snd))).lintegral_prod_right') hC
