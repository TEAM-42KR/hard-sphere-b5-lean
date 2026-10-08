import HardSphereB5Lean.Definitions.Def_Gnomonic_forward
set_option autoImplicit false
noncomputable section
open MeasureTheory SphereGeom
open scoped ENNReal
namespace Gnomonic
def unitDisk : Set (ℝ × ℝ) := {y | y.1 ^ 2 + y.2 ^ 2 < 1}

def upperGraph (y : ℝ × ℝ) : E3 :=
  WithLp.toLp 2 ![y.1, y.2, Real.sqrt (1 - y.1 ^ 2 - y.2 ^ 2)]

def graphDensity (y : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (1 - y.1 ^ 2 - y.2 ^ 2))⁻¹)

def planeProjection (u : E3) : ℝ × ℝ := (u 0, u 1)

def upperHemisphere : Set E3 := {u | ‖u‖ = 1 ∧ 0 < u 2}
def radialPair (x : Plane) : ℝ × ℝ :=
  (x 0 / Real.sqrt (1+‖x‖^2), x 1 / Real.sqrt (1+‖x‖^2))
end Gnomonic
