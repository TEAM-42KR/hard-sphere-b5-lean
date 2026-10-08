import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_radial_density_fst_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (J : X → ENNReal) (w : Y → ENNReal) (hJ : Measurable J) (hw : Measurable w) :
    ((μ.prod ν).withDensity (fun z : X × Y => J z.1 * w z.2)).map Prod.fst =
      (∫⁻ y, w y ∂ν) • μ.withDensity J := by
  rw [← prod_withDensity hJ hw]
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply measurable_fst hS, Measure.smul_apply]
  have hpre : Prod.fst ⁻¹' S = S ×ˢ (Set.univ : Set Y) := by ext z; simp
  rw [hpre, Measure.prod_prod, withDensity_apply w MeasurableSet.univ, Measure.restrict_univ]
  exact mul_comm _ _
