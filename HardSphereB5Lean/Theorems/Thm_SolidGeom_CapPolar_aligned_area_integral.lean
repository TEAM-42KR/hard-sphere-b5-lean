import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_aligned_area_integral
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_AlignedCap
set_option autoImplicit false
noncomputable section
open MeasureTheory

theorem SolidGeom.CapPolar.aligned_area_integral :
    ∀ (P : SolidGeom.CapPolar.Profile)
    (j : Fin 3) (C : SolidGeom.CapPolar.AlignedCap P j) (a b : ℝ), (∫ φ in a..b, (1-Real.cos (P.rho j φ)))=
      SolidGeom.CapPolar.areaPrimitive C.A (P.height j) (b-C.δ)-
        SolidGeom.CapPolar.areaPrimitive C.A (P.height j) (a-C.δ) :=
  @proof_SolidGeom_CapPolar_aligned_area_integral
