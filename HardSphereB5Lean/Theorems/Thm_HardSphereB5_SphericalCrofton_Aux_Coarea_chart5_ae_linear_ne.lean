import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_chart5_ae_linear_ne
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.chart5_ae_linear_ne :
    ∀ (L : Chart5 →ₗ[ℝ] ℝ) (hL : L ≠ 0) (c : ℝ), ∀ᵐ y : Chart5 ∂volume, L y ≠ c :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_chart5_ae_linear_ne
