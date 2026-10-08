import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_moment_eq_polar_sectors
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_Profile
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SolidGeom.CapPolar.moment_eq_polar_sectors :
    ∀ (P : SolidGeom.CapPolar.Profile), (∫ u in SolidGeom.CapPolar.caps P, u ∂dOmega) = ∑ j : Fin 3, ∫ φ in SolidGeom.CapPolar.sector P j, SolidGeom.CapPolar.momentDensity P j φ :=
  @proof_SolidGeom_CapPolar_moment_eq_polar_sectors
