import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

noncomputable section
open MeasureTheory
open SphereGeom (E3)

namespace Gnomonic
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def forward (n u : E3) : E3 := (inner ℝ u n)⁻¹ • u - n

def chartFrame (R : E3 ≃ₗᵢ[ℝ] E3) (u : E3) : Plane :=
  WithLp.toLp 2 ![(R.symm u) 0 / (R.symm u) 2, (R.symm u) 1 / (R.symm u) 2]

def inverseFrame (R : E3 ≃ₗᵢ[ℝ] E3) (x : Plane) : E3 :=
  R ((Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ • WithLp.toLp 2 ![x 0, x 1, 1])

def hemisphereFrame (R : E3 ≃ₗᵢ[ℝ] E3) : Set E3 :=
  {u | ‖u‖ = 1 ∧ 0 < (R.symm u) 2}

def density (x : Plane) : ℝ := Real.rpow (1 + ‖x‖ ^ 2) (-(3 / 2 : ℝ))

def planarMeasure : Measure Plane :=
  volume.withDensity (fun x => ENNReal.ofReal (density x))

end Gnomonic
