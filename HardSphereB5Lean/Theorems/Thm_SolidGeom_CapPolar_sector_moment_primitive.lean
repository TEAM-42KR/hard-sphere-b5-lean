import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_sector_moment_primitive
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_momentPrimitive
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SolidGeom.CapPolar.sector_moment_primitive :
    ∀ (p a b : SphereGeom.E3)
  (A h ψ₁ ψ₂ : ℝ) (hh : 0 < h) (hA : h < A) (hA1 : A ≤ 1)
  (hframe : Orthonormal ℝ (fun k : Fin 3 => ![p,a,b] k)), (∫ ψ in ψ₁..ψ₂, ∫ ρ in (0)..(SolidGeom.CapPolar.exitRadius A h ψ),
    Real.sin ρ • SolidGeom.CapPolar.polarRay p a b ψ ρ) =
  SolidGeom.CapPolar.momentPrimitive p a b A h ψ₂ -
    SolidGeom.CapPolar.momentPrimitive p a b A h ψ₁ :=
  @proof_SolidGeom_CapPolar_sector_moment_primitive
