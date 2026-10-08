import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
noncomputable section
open scoped Classical
namespace HardSphereB5.SphericalCrofton.Aux.Coarea

def sourceIncidence : Set Chart5 := {x | offAxis (sourceCenter x) ∧ sourceCenter x ∈ LamC ∧
  Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1 ∧
  x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)) ∧
  x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x)) ∧
  sourceEndpointA x ∈ FA ∧ sourceEndpointB x ∈ FB ∧
  0 < dist (sourceEndpointA x) (sourceEndpointB x) ∧ dist (sourceEndpointA x) (sourceEndpointB x) < 1}

def targetIncidence : Set Chart5 := {y |
  y 0 ∈ Set.Icc (1/2 : ℝ) 1 ∧ y 2 ∈ Set.Icc (-1 : ℝ) (-1/2) ∧
  y 1 ∈ Set.Icc (-Real.pi) Real.pi ∧ y 3 ∈ Set.Icc (-Real.pi) Real.pi ∧
  y 4 ∈ Set.Icc (-Real.pi) Real.pi ∧
  0 < dist (targetEndpointA y) (targetEndpointB y) ∧
  dist (targetEndpointA y) (targetEndpointB y) < 1 ∧ targetCenter y ∈ LamC}

def sourceTest (G : Pt → Pt → Pt → ℝ) (x : Chart5) : ℝ :=
  G (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x) /
    (‖sourceCenter x‖ * ‖sourceCenter x-e‖)

def targetTest (G : Pt → Pt → Pt → ℝ) (y : Chart5) : ℝ :=
  G (targetCenter y) (targetEndpointA y) (targetEndpointB y) /
    dist (targetEndpointA y) (targetEndpointB y)

end HardSphereB5.SphericalCrofton.Aux.Coarea
