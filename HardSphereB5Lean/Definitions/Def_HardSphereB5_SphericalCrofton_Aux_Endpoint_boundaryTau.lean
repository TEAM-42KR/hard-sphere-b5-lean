import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
namespace HardSphereB5.SphericalCrofton.Aux.Endpoint

def boundaryTau (D u : Pt) : Pt := if u ∈ arcA D then tanA D u else tanB D u
def boundaryMu (D : Pt) : Measure Pt := arcMeasure.restrict (arcA D ∪ arcB D)
def pairMu (D : Pt) : Measure (Pt × Pt) := (boundaryMu D).prod (boundaryMu D)
def pairPole (q : Pt × Pt) : Pt := unitDir (cross q.1 q.2)
def pairDelta (q : Pt × Pt) : ℝ := arccos (inner ℝ q.1 q.2)
def pairDens (D : Pt) (q : Pt × Pt) : ℝ :=
  santaloDens q.1 q.2 (boundaryTau D q.1) (boundaryTau D q.2)
def weightedPairMu (D : Pt) : Measure (Pt × Pt) :=
  (pairMu D).withDensity (fun q => ENNReal.ofReal (pairDens D q))
def hitPoleSet (D : Pt) : Set Pt := {p | 0 < chordLen (SigmaD D) (greatCircle p)}
def pairKernel (f : Kern) (D : Pt) (q : Pt × Pt) : ℝ :=
  cutKern f (pairDelta q) * pairDens D q
end HardSphereB5.SphericalCrofton.Aux.Endpoint
