import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
set_option autoImplicit false

noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
namespace HardSphereB5.SphericalCrofton.Aux.Coarea

abbrev Chart5 := EuclideanSpace ℝ (Fin 5)

def pack5 (a b c d f : ℝ) : Chart5 :=
  a • EuclideanSpace.single 0 1 + b • EuclideanSpace.single 1 1 +
    c • EuclideanSpace.single 2 1 + d • EuclideanSpace.single 3 1 +
    f • EuclideanSpace.single 4 1

def sourceCenter (x : Chart5) : Pt := x 0 • e + x 1 • e1 + x 2 • e2

def sourceEndpointA (x : Chart5) : Pt := sourceCenter x + u (sourceCenter x) (x 3)
def sourceEndpointB (x : Chart5) : Pt := sourceCenter x + v (sourceCenter x) (x 4)

def phase (a b : ℝ) : ℂ := ⟨a,b⟩
def azimuth (p : Pt) : ℝ := Complex.arg (phase (p 1) (p 2))

def centerFrame0 (d : Pt) : Pt := unitDir (e - (inner ℝ (unitDir d) e) • unitDir d)
def centerFrame1 (d : Pt) : Pt := cross (unitDir d) (centerFrame0 d)

def centerPhase (D p p' : Pt) : ℂ :=
  phase (inner ℝ (centerFrame0 (p'-p)) (D-midpoint ℝ p p'))
    (inner ℝ (centerFrame1 (p'-p)) (D-midpoint ℝ p p'))

def Phi (x : Chart5) : Chart5 :=
  let D := sourceCenter x
  let p := sourceEndpointA x
  let p' := sourceEndpointB x
  pack5 (p 0) (azimuth p) (p' 0 - 1) (azimuth p') (Complex.arg (centerPhase D p p'))

def endpointCylinder (h φ : ℝ) : Pt :=
  (Real.sqrt (1-h^2) * Real.cos φ) • e1 +
    (Real.sqrt (1-h^2) * Real.sin φ) • e2 + h • e

def targetEndpointA (y : Chart5) : Pt := endpointCylinder (y 0) (y 1)
def targetEndpointB (y : Chart5) : Pt := e + endpointCylinder (y 2) (y 3)

def targetCenter (y : Chart5) : Pt :=
  let p := targetEndpointA y
  let p' := targetEndpointB y
  let d := p'-p
  midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) •
    (Real.cos (y 4) • centerFrame0 d + Real.sin (y 4) • centerFrame1 d)

def sourcePhaseA (D p : Pt) : ℂ :=
  phase (inner ℝ (EA D 0) (p-D-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)) (inner ℝ (EA D 1) (p-D-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D))
def sourcePhaseB (D p' : Pt) : ℂ :=
  phase (inner ℝ (EB D 0) (p'-D-HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D)) (inner ℝ (EB D 1) (p'-D-HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D))

def Psi (y : Chart5) : Chart5 :=
  let D := targetCenter y
  pack5 (D 0) (D 1) (D 2)
    (Complex.arg (sourcePhaseA D (targetEndpointA y)))
    (Complex.arg (sourcePhaseB D (targetEndpointB y)))

def sourceRegular (x : Chart5) : Prop :=
  let D := sourceCenter x
  let p := sourceEndpointA x
  let p' := sourceEndpointB x
  offAxis D ∧ D ∈ LamC ∧ p ∈ FA ∧ p' ∈ FB ∧
    0 < dist p p' ∧ dist p p' < 1 ∧
    x 3 ∈ Set.Ioo (-Real.pi) Real.pi ∧ x 4 ∈ Set.Ioo (-Real.pi) Real.pi ∧
    |p 0| < 1 ∧ |p' 0-1| < 1 ∧
    centerFrame0 (p'-p) ≠ 0 ∧
    phase (p 1) (p 2) ∈ Complex.slitPlane ∧
    phase (p' 1) (p' 2) ∈ Complex.slitPlane ∧
    centerPhase D p p' ∈ Complex.slitPlane

end HardSphereB5.SphericalCrofton.Aux.Coarea
