import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_Profile
import Mathlib
set_option autoImplicit false
noncomputable section
def SolidGeom.CapPolar.frameExitCos (A h B:ℝ):ℝ:=
  (A*h-B*Real.sqrt (A^2+B^2-h^2))/(A^2+B^2)
def SolidGeom.CapPolar.frameExitSin (A h B:ℝ):ℝ:=
  (B*h+A*Real.sqrt (A^2+B^2-h^2))/(A^2+B^2)
def SolidGeom.CapPolar.frameExitRadius (A h B:ℝ):ℝ:=
  Real.arccos (SolidGeom.CapPolar.frameExitCos A h B)
