import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_radial_moment_integral
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
set_option autoImplicit false
noncomputable section
open MeasureTheory

theorem SolidGeom.CapPolar.radial_moment_integral :
    ∀ (p a b : SphereGeom.E3) (ψ R : ℝ), (∫ ρ in (0)..R, Real.sin ρ • SolidGeom.CapPolar.polarRay p a b ψ ρ)=
      ((R-Real.sin R*Real.cos R)/2) • SolidGeom.CapPolar.capDirection a b ψ+
      ((Real.sin R)^2/2) • p :=
  @proof_SolidGeom_CapPolar_radial_moment_integral
