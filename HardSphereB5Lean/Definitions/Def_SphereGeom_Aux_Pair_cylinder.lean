import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
noncomputable section
namespace SphereGeom.Aux.Pair
open MeasureTheory
def cylinder (z φ : ℝ) : SphereGeom.E3 := WithLp.toLp 2
  ![Real.sqrt (1-z^2) * Real.cos φ, Real.sqrt (1-z^2) * Real.sin φ, z]
def frame1 (φ : ℝ) : SphereGeom.E3 := WithLp.toLp 2 ![-Real.sin φ, Real.cos φ, 0]
def frame2 (z φ : ℝ) : SphereGeom.E3 := WithLp.toLp 2 ![-z * Real.cos φ, -z * Real.sin φ, Real.sqrt (1-z^2)]
def fiber (z φ t : ℝ) : SphereGeom.E3 := SphereGeom.circlePt 0 (frame1 φ) (frame2 z φ) 1 t
def meridian (z t : ℝ) : SphereGeom.E3 := WithLp.toLp 2
  ![-Real.sqrt (1-z^2) * Real.cos t, z, Real.sqrt (1-z^2) * Real.sin t]
def reciprocal (x : SphereGeom.E3) (ψ : ℝ) : SphereGeom.E3 :=
  (x 0 / Real.sqrt (1-(x 2)^2)) • frame1 ψ + (x 1 / Real.sqrt (1-(x 2)^2)) • frame2 (x 2) ψ
end SphereGeom.Aux.Pair
