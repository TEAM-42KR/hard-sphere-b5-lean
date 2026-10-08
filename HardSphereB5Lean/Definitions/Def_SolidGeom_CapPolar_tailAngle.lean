import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
set_option autoImplicit false
noncomputable section
open SphereGeom SolidGeom.CapPolar
open scoped RealInnerProductSpace
def SolidGeom.CapPolar.tailAngle (A h ψ : ℝ) : ℝ :=
  Real.arcsin (capBeta A*Real.sin ψ/capK h)
def SolidGeom.CapPolar.capRadialBasis (p a b : E3) (A h ψ : ℝ) : E3 :=
  exitCos A h ψ • capDirection a b ψ-exitSin A h ψ • p
def SolidGeom.CapPolar.capAzimuthBasis (a b : E3) (ψ : ℝ) : E3 :=
  Real.cos ψ • b-Real.sin ψ • a
def SolidGeom.CapPolar.capCorner (u n m : E3) : ℝ :=
  Complex.arg ⟨inner ℝ (SphereGeom.cross n u) (SphereGeom.cross m u),
    inner ℝ u (SphereGeom.cross (SphereGeom.cross n u) (SphereGeom.cross m u))⟩
