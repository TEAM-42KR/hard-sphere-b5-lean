import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_momentPrimitive
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
def SolidGeom.CapPolar.capAxis (p a : E3) (A : ℝ) : E3 := A • p+capBeta A • a
def SolidGeom.CapPolar.capDirection (a b : E3) (ψ : ℝ) : E3 := Real.cos ψ • a+Real.sin ψ • b
def SolidGeom.CapPolar.capExitPoint (p a b : E3) (A h ψ : ℝ) : E3 :=
  exitCos A h ψ • p+exitSin A h ψ • SolidGeom.CapPolar.capDirection a b ψ
def SolidGeom.CapPolar.radialEdgeCorrection (p a b : E3) (A h ψ : ℝ) : E3 :=
  (exitRadius A h ψ/2) • SphereGeom.cross p (SolidGeom.CapPolar.capDirection a b ψ)
def SolidGeom.CapPolar.radialEdgeCorrectionOfPoint (p u : E3) : E3 :=
  (Real.arccos (inner ℝ p u)/(2*Real.sqrt (1-(inner ℝ p u)^2))) • SphereGeom.cross p u

