import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_map_withDensity_comp
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.map_withDensity_comp :
    ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (f : X → Y) (w : Y → ENNReal) (hf : Measurable f) (hw : Measurable w), (μ.withDensity (fun x => w (f x))).map f = (μ.map f).withDensity w :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_map_withDensity_comp
