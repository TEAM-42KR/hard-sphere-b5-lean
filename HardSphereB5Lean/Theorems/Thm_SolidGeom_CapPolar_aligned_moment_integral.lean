import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_aligned_moment_integral
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_AlignedCap
set_option autoImplicit false
noncomputable section
open MeasureTheory

theorem SolidGeom.CapPolar.aligned_moment_integral :
    ∀ (P : SolidGeom.CapPolar.Profile)
    (j : Fin 3) (C : SolidGeom.CapPolar.AlignedCap P j) (a b : ℝ), (∫ φ in a..b, SolidGeom.CapPolar.momentDensity P j φ)=
      SolidGeom.CapPolar.momentPrimitive (P.e 2) C.a C.b C.A (P.height j) (b-C.δ)-
        SolidGeom.CapPolar.momentPrimitive (P.e 2) C.a C.b C.A (P.height j) (a-C.δ) :=
  @proof_SolidGeom_CapPolar_aligned_moment_integral
