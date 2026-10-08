import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_sector_width_sum
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_Profile
set_option autoImplicit false
open MeasureTheory
noncomputable section

theorem SolidGeom.CapPolar.sector_width_sum :
    ∀ (P : SolidGeom.CapPolar.Profile), (∑ j : Fin 3, ∫ φ in SolidGeom.CapPolar.sector P j, (1:ℝ))=2*Real.pi :=
  @proof_SolidGeom_CapPolar_sector_width_sum
