import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_profile_of_frame
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_frameExitRadius
set_option autoImplicit false
open MeasureTheory Real
noncomputable section
open scoped RealInnerProductSpace

theorem SolidGeom.CapPolar.profile_of_frame :
    ∀ (e:Fin 3→SphereGeom.E3) (he:Orthonormal ℝ e)
    (n:Fin 3→SphereGeom.E3) (hn:∀j,‖n j‖=1) (h:Fin 3→ℝ)
    (hh:∀ j, 0 < h j) (hp:∀j,h j < inner ℝ (n j) (e 2)), ∃ P :SolidGeom.CapPolar.Profile,P.e=e ∧ P.normal=n ∧ P.height=h ∧
      ∀ j ψ,P.rho j ψ=SolidGeom.CapPolar.frameExitRadius (inner ℝ (n j) (e 2)) (h j)
        (Real.cos ψ*inner ℝ (n j) (e 0)+Real.sin ψ*inner ℝ (n j) (e 1)) :=
  @proof_SolidGeom_CapPolar_profile_of_frame
