import Mathlib
set_option autoImplicit false
noncomputable section
namespace SolidGeom.CapPolar
def capBeta (A:ℝ):ℝ:=Real.sqrt (1-A^2)
def capK (h:ℝ):ℝ:=Real.sqrt (1-h^2)
def rayRadical (A h ψ:ℝ):ℝ:=Real.sqrt ((capK h)^2-(capBeta A)^2*(Real.sin ψ)^2)
def rayDenom (A ψ:ℝ):ℝ:=1-(capBeta A)^2*(Real.sin ψ)^2
def exitCos (A h ψ:ℝ):ℝ:=(A*h-capBeta A*Real.cos ψ*rayRadical A h ψ)/rayDenom A ψ
def exitSin (A h ψ:ℝ):ℝ:=(capBeta A*h*Real.cos ψ+A*rayRadical A h ψ)/rayDenom A ψ
def continuousAzimuth (A ψ:ℝ):ℝ:=ψ-Real.arctan ((1-A)*Real.sin ψ*Real.cos ψ/((Real.cos ψ)^2+A*(Real.sin ψ)^2))
def tailPrimitive (h k t:ℝ):ℝ:=Real.arcsin (t/k)-h*Real.arctan (h*t/Real.sqrt (k^2-t^2))
def areaPrimitive (A h ψ:ℝ):ℝ:=ψ-h*continuousAzimuth A ψ+tailPrimitive h (capK h) (capBeta A*Real.sin ψ)
def areaDensity (A h ψ:ℝ):ℝ:=1-exitCos A h ψ
end SolidGeom.CapPolar
