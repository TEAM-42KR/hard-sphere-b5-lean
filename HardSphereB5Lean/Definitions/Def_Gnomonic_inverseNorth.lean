import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
noncomputable section
open SphereGeom
namespace Gnomonic
abbrev E2 := EuclideanSpace ℝ (Fin 2)

def north : E3 := EuclideanSpace.single (2 : Fin 3) 1

def northPlaneInclusion : E2 →L[ℝ] E3 :=
  (innerSL ℝ (EuclideanSpace.single (0 : Fin 2) 1)).smulRight
      (EuclideanSpace.single (0 : Fin 3) 1) +
  (innerSL ℝ (EuclideanSpace.single (1 : Fin 2) 1)).smulRight
      (EuclideanSpace.single (1 : Fin 3) 1)

def northLift (x : E2) : E3 := northPlaneInclusion x + north

def northRadius (x : E2) : ℝ := Real.sqrt (1 + ‖x‖ ^ 2)

def inverseNorth (x : E2) : E3 := (northRadius x)⁻¹ • northLift x

def projectionNorth (u : E3) : E2 := WithLp.toLp 2 ![u 0 / u 2, u 1 / u 2]

def inverseNorthDeriv (x : E2) : E2 →L[ℝ] E3 :=
  (northRadius x)⁻¹ • northPlaneInclusion -
  ((northRadius x)^3)⁻¹ • (innerSL ℝ x).smulRight (northLift x)

def northGramMatrix (x : E2) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  inner ℝ (fderiv ℝ inverseNorth x (EuclideanSpace.single i 1))
    (fderiv ℝ inverseNorth x (EuclideanSpace.single j 1))
end Gnomonic
