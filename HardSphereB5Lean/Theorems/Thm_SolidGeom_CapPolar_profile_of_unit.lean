import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_profile_of_unit
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_profile_of_frame
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace

theorem SolidGeom.CapPolar.profile_of_unit :
    ∀ (p : SphereGeom.E3) (hp : ‖p‖ = 1)
    (n : Fin 3 → SphereGeom.E3) (hn : ∀ j, ‖n j‖ = 1) (h : Fin 3 → ℝ)
    (hh : ∀ j, 0 < h j) (hi : ∀ j, h j < inner ℝ (n j) p), ∃ P : SolidGeom.CapPolar.Profile, P.e 2 = p ∧ P.normal = n ∧ P.height = h :=
  @proof_SolidGeom_CapPolar_profile_of_unit
