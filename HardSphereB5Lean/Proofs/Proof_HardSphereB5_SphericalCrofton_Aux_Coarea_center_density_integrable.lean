import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_density_integrable :
    IntegrableOn (fun D : Pt => (‖D‖ * ‖D-e‖)⁻¹) LamC volume  := by
  have hloc : LocallyIntegrable (fun D : Pt => ‖D‖⁻¹) volume := by
    apply locallyIntegrable_of_norm_le_rpow (α := 1) (C := 1)
      (by simp [Pt, SphereGeom.E3]) (by simp [Pt, SphereGeom.E3])
    · filter_upwards [] with D
      simp [Real.rpow_neg_one, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg D))]
    · exact measurable_norm.inv.aestronglyMeasurable
  have hc : IsCompact LamC := (isCompact_closedBall (0 : Pt) 1).inter_right
    (Metric.isClosed_closedBall : IsClosed (Metric.closedBall e 1))
  have hiA := hloc.integrableOn_isCompact hc
  have hiB : IntegrableOn (fun D : Pt => ‖D-e‖⁻¹) LamC volume := by
    have hme := (MeasurableEquiv.addRight (-e : Pt)).measurableEmbedding
    have hp := measurePreserving_add_right (volume : Measure Pt) (-e)
    have hh := (hp.integrableOn_image hme).mp
      (hloc.integrableOn_isCompact (hc.image (continuous_id.add continuous_const)))
    simpa [Function.comp_def, sub_eq_add_neg] using hh
  refine (hiA.add hiB).mono' ((measurable_norm.mul
    (measurable_id.sub measurable_const).norm).inv.aestronglyMeasurable) ?_
  filter_upwards [] with D
  have ha := norm_nonneg D
  have hb := norm_nonneg (D-e)
  by_cases hza : ‖D‖ = 0
  · simp [hza]
  by_cases hzb : ‖D-e‖ = 0
  · simp [hzb]
  have hap : 0 < ‖D‖ := lt_of_le_of_ne ha (Ne.symm hza)
  have hbp : 0 < ‖D-e‖ := lt_of_le_of_ne hb (Ne.symm hzb)
  have hab : 1 ≤ ‖D‖ + ‖D-e‖ := by
    have h := norm_add_le D (e-D)
    have he : D+(e-D)=e := by abel
    rw [he, norm_sub_rev e D] at h
    simpa [HardSphereB5.Lean.e] using h
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (mul_nonneg ha hb))]
  have hcalc : (‖D‖⁻¹ + ‖D-e‖⁻¹) * (‖D‖ * ‖D-e‖) = ‖D‖+‖D-e‖ := by
    field_simp
    ring
  rw [← one_div]
  apply (div_le_iff₀ (mul_pos hap hbp)).mpr
  change 1 ≤ (‖D‖⁻¹ + ‖D-e‖⁻¹) * (‖D‖ * ‖D-e‖)
  rw [hcalc]
  exact hab

