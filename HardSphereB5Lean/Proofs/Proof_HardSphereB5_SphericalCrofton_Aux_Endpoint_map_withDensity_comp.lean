import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (w : Y → ENNReal)
    (hf : Measurable f) (hw : Measurable w) :
    (μ.withDensity (fun x => w (f x))).map f = (μ.map f).withDensity w := by
  apply Measure.ext
  intro T hT
  rw [Measure.map_apply hf hT, withDensity_apply _ (hf hT), withDensity_apply _ hT,
    setLIntegral_map hT hw hf]
