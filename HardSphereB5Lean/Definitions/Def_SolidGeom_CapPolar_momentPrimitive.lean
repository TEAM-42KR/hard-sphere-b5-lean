import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_areaPrimitive
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

noncomputable section
open MeasureTheory Real SphereGeom

def SolidGeom.CapPolar.exitRadius (A h ψ : ℝ) : ℝ :=
  Real.arccos (SolidGeom.CapPolar.exitCos A h ψ)

def SolidGeom.CapPolar.momentAzimuth (A h ψ : ℝ) : ℝ :=
  SolidGeom.CapPolar.continuousAzimuth A ψ +
    Real.arctan (h*SolidGeom.CapPolar.capBeta A*Real.sin ψ /
      SolidGeom.CapPolar.rayRadical A h ψ)

def SolidGeom.CapPolar.momentPrimitive (p a b : E3) (A h ψ : ℝ) : E3 :=
  let β := SolidGeom.CapPolar.capBeta A
  let k2 := 1-h^2
  let C := SolidGeom.CapPolar.exitCos A h ψ
  let S := SolidGeom.CapPolar.exitSin A h ψ
  let ρ := SolidGeom.CapPolar.exitRadius A h ψ
  let φ := SolidGeom.CapPolar.momentAzimuth A h ψ
  ((k2*A*φ+h*β*S*Real.sin ψ)/2) • p +
  ((k2*β*φ-h*A*S*Real.sin ψ+ρ*Real.sin ψ)/2) • a +
  ((h*(A*S*Real.cos ψ-β*C)-ρ*Real.cos ψ)/2) • b

def SolidGeom.CapPolar.polarRay (p a b : E3) (ψ ρ : ℝ) : E3 :=
  Real.cos ρ • p + Real.sin ρ • (Real.cos ψ • a+Real.sin ψ • b)
