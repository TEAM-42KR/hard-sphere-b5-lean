import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_cap_corner_tail_angle
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_tailAngle
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace

theorem SolidGeom.CapPolar.cap_corner_tail_angle :
    ∀ (p a₁ b₁ a₂ b₂ : SphereGeom.E3)
    (A₁ h₁ ψ₁ A₂ h₂ ψ₂ : ℝ)
    (hp : inner ℝ p p=1)
    (ha₁ : inner ℝ a₁ a₁=1) (hpa₁ : inner ℝ p a₁=0) (hb₁ : SphereGeom.cross p a₁=b₁)
    (ha₂ : inner ℝ a₂ a₂=1) (hpa₂ : inner ℝ p a₂=0) (hb₂ : SphereGeom.cross p a₂=b₂)
    (hh₁ : 0<h₁) (hA₁ : h₁<A₁) (hA₁1 : A₁≤1)
    (hh₂ : 0<h₂) (hA₂ : h₂<A₂) (hA₂1 : A₂≤1)
    (hu : SolidGeom.CapPolar.capExitPoint p a₁ b₁ A₁ h₁ ψ₁ =
      SolidGeom.CapPolar.capExitPoint p a₂ b₂ A₂ h₂ ψ₂), SolidGeom.CapPolar.capCorner (SolidGeom.CapPolar.capExitPoint p a₁ b₁ A₁ h₁ ψ₁)
      (SolidGeom.CapPolar.capAxis p a₁ A₁) (SolidGeom.CapPolar.capAxis p a₂ A₂) =
      SolidGeom.CapPolar.tailAngle A₂ h₂ ψ₂-SolidGeom.CapPolar.tailAngle A₁ h₁ ψ₁ :=
  @proof_SolidGeom_CapPolar_cap_corner_tail_angle
