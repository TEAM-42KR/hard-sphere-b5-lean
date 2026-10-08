import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open SphereGeom (E3)

namespace Gnomonic

structure CapFrame (a e1 e2 : E3) : Prop where
  aa : ⟪a, a⟫ = 1
  e11 : ⟪e1, e1⟫ = 1
  e22 : ⟪e2, e2⟫ = 1
  ae1 : ⟪a, e1⟫ = 0
  ae2 : ⟪a, e2⟫ = 0
  e12 : ⟪e1, e2⟫ = 0

def project (n u : E3) : E3 := ⟪u, n⟫⁻¹ • u - n

def projectVelocity (n u v : E3) : E3 :=
  ⟪u, n⟫⁻¹ • v + (-⟪v, n⟫ / ⟪u, n⟫ ^ 2) • u

def capArc (a e1 e2 : E3) (h t : ℝ) : E3 :=
  h • a + Real.sqrt (1 - h ^ 2) • (Real.cos t • e1 + Real.sin t • e2)

def capVelocity (e1 e2 : E3) (h t : ℝ) : E3 :=
  Real.sqrt (1 - h ^ 2) • (-Real.sin t • e1 + Real.cos t • e2)

def projectedArc (n a e1 e2 : E3) (h t : ℝ) : E3 :=
  project n (capArc a e1 e2 h t)

def visible (n a e1 e2 : E3) (h : ℝ) : Set ℝ :=
  {t | 0 < ⟪capArc a e1 e2 h t, n⟫}

end Gnomonic
