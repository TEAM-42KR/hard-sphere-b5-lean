import Mathlib
set_option autoImplicit false

noncomputable section
open MeasureTheory

namespace SphereGeom

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def sphereMeasure (c : E3) : Measure E3 :=
  ((volume : Measure E3).toSphere).map (fun u : Metric.sphere (0 : E3) 1 => c + (u : E3))

def dOmega : Measure E3 := sphereMeasure 0

def arcMeasure : Measure E3 := Measure.hausdorffMeasure 1

def cap (n : E3) (h : ℝ) : Set E3 := {u | ‖u‖ = 1 ∧ h ≤ inner ℝ n u}

def greatCircle (p : E3) : Set E3 := {u | ‖u‖ = 1 ∧ inner ℝ p u = 0}

def gcIntegral (F : Set E3 → ℝ) : ℝ := (1 / 2) * ∫ p, F (greatCircle p) ∂dOmega

def cross (u v : E3) : E3 := WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

def circlePt (c e₁ e₂ : E3) (r t : ℝ) : E3 := c + r • (Real.cos t • e₁ + Real.sin t • e₂)

end SphereGeom
