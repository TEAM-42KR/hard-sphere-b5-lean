import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_sector_area_primitive
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_areaPrimitive
set_option autoImplicit false
open MeasureTheory Real
noncomputable section

theorem SolidGeom.CapPolar.sector_area_primitive :
    ∀ (A h a b:ℝ)
    (hh:0<h) (hA:h<A) (hA1:A≤1), (∫ψ in a..b, SolidGeom.CapPolar.areaDensity A h ψ)=
      SolidGeom.CapPolar.areaPrimitive A h b-SolidGeom.CapPolar.areaPrimitive A h a :=
  @proof_SolidGeom_CapPolar_sector_area_primitive
