import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
namespace HardSphereB5.SphericalCrofton.Aux.MovingArc

def rawA (D : Pt) : Pt := e - (inner ℝ (nAv D) e) • nAv D
def rawB (D : Pt) : Pt := -e - (inner ℝ (nBv D) (-e)) • nBv D
def EA (D : Pt) : Fin 2 → Pt := ![unitDir (rawA D), cross (nAv D) (unitDir (rawA D))]
def EB (D : Pt) : Fin 2 → Pt := ![unitDir (rawB D), -cross (nBv D) (unitDir (rawB D))]
def rA (D : Pt) : ℝ := Real.sqrt (1 - ‖D‖^2 / 4)
def rB (D : Pt) : ℝ := Real.sqrt (1 - ‖D-e‖^2 / 4)
def cA (D : Pt) : Pt := (-1/2 : ℝ) • D
def cB (D : Pt) : Pt := (1/2 : ℝ) • (e-D)
def cutA (D : Pt) : ℝ := (1-inner ℝ D e)/(2*rA D*‖rawA D‖)
def cutB (D : Pt) : ℝ := (inner ℝ D e)/(2*rB D*‖rawB D‖)
def halfA (D : Pt) : ℝ := Real.arccos (cutA D)
def halfB (D : Pt) : ℝ := Real.arccos (cutB D)
def u (D : Pt) : ℝ → Pt := circlePt (cA D) (EA D 0) (EA D 1) (rA D)
def v (D : Pt) : ℝ → Pt := circlePt (cB D) (EB D 0) (EB D 1) (rB D)
end HardSphereB5.SphericalCrofton.Aux.MovingArc
