import HardSphereB5Lean.Definitions.Def_Gnomonic_inverseNorth
import HardSphereB5Lean.Definitions.Def_SolidGeom_ClassicalInputs_SurfaceCalculusInputs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Real
open scoped RealInnerProductSpace
namespace HardSphereB5.Lean.Geometry.PathCore.BulkCalculus
open SphereGeom (E3 dOmega)
open SolidGeom.ClassicalInputs (E2 e0 e1 cross2)
def BC_A (x : E2) : ℝ := 1 + (x 0 ^ 2 + x 1 ^ 2)

def BC_invA (x : E2) : ℝ := (BC_A x)⁻¹

def BC_coordL (k : Fin 2) : E2 →L[ℝ] ℝ := innerSL ℝ (EuclideanSpace.single k 1)

def BC_dA (x : E2) : E2 →L[ℝ] ℝ :=
  (2*x 0) • BC_coordL 0 + (2*x 1) • BC_coordL 1

def BC_momentP (k : Fin 3) (x : E2) : ℝ :=
  ![0, BC_invA x, -x 1 * BC_invA x] k

def BC_momentQ (k : Fin 3) (x : E2) : ℝ :=
  ![-BC_invA x, 0, x 0 * BC_invA x] k

def BC_momentDensity (k : Fin 3) (x : E2) : ℝ :=
  ![x 0, x 1, 1] k * (BC_A x ^ 2)⁻¹

def BC_radius (x : E2) : ℝ := Real.sqrt (BC_A x)

def BC_connectionDen (x : E2) : ℝ := BC_radius x*(BC_radius x+1)

def BC_connectionInv (x : E2) : ℝ := (BC_connectionDen x)⁻¹

def BC_connectionP (x : E2) : ℝ := x 1*BC_connectionInv x

def BC_connectionQ (x : E2) : ℝ := -x 0*BC_connectionInv x

def BC_frameLift (x : E2) : E3 :=
  Gnomonic.northPlaneInclusion x + (BC_radius x+1) • Gnomonic.north

def BC_frame1 (x : E2) : E3 := EuclideanSpace.single 0 1 -
  (x 0*BC_connectionInv x) • BC_frameLift x

def BC_frame2 (x : E2) : E3 := EuclideanSpace.single 1 1 -
  (x 1*BC_connectionInv x) • BC_frameLift x

def BC_capPrimitive (a e : E3) (h t : ℝ) : E3 :=
  ((1-h^2)*t) • a + (h*Real.sqrt (1-h^2)) •
    (-Real.sin t • e+Real.cos t • SphereGeom.cross a e)

def BC_coord3L (k : Fin 3) : E3 →L[ℝ] ℝ := innerSL ℝ (EuclideanSpace.single k 1)

def BC_frameTangent (g : ℝ → E2) (t : ℝ) : E2 :=
  let u' := deriv (fun s => Gnomonic.inverseNorth (g s)) t
  WithLp.toLp 2 ![inner ℝ (BC_frame1 (g t)) u',
                  inner ℝ (BC_frame2 (g t)) u']

def BC_sphericalRate (g : ℝ → E2) (t : ℝ) : ℝ :=
  let u := fun s => Gnomonic.inverseNorth (g s)
  inner ℝ (u t) (SphereGeom.cross (deriv u t) (deriv (deriv u) t)) /
    ‖deriv u t‖^2

end HardSphereB5.Lean.Geometry.PathCore.BulkCalculus
