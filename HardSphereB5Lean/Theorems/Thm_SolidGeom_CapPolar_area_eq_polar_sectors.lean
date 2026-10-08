import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_area_eq_polar_sectors
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_Profile
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SolidGeom.CapPolar.area_eq_polar_sectors :
    ∀ (P : SolidGeom.CapPolar.Profile), (dOmega (SolidGeom.CapPolar.caps P)).toReal = ∑ j : Fin 3, ∫ φ in SolidGeom.CapPolar.sector P j, (1-Real.cos (P.rho j φ)) :=
  @proof_SolidGeom_CapPolar_area_eq_polar_sectors
