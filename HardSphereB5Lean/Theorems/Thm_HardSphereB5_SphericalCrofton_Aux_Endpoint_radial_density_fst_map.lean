import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_radial_density_fst_map
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.radial_density_fst_map :
    ∀ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (J : X → ENNReal) (w : Y → ENNReal) (hJ : Measurable J) (hw : Measurable w), ((μ.prod ν).withDensity (fun z : X × Y => J z.1 * w z.2)).map Prod.fst = (∫⁻ y, w y ∂ν) • μ.withDensity J :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_radial_density_fst_map
