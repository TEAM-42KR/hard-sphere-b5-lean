import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_Profile
set_option autoImplicit false
noncomputable section
open SphereGeom SolidGeom.CapPolar
open scoped RealInnerProductSpace
structure SolidGeom.CapPolar.AlignedCap (P : Profile) (j : Fin 3) where
  a : E3
  b : E3
  A : ℝ
  δ : ℝ
  frame : Orthonormal ℝ (fun k : Fin 3 => ![P.e 2,a,b] k)
  oriented : SphereGeom.cross (P.e 2) a=b
  normal_eq : P.normal j=capAxis (P.e 2) a A
  pole_cos : A=inner ℝ (P.normal j) (P.e 2)
  bounds : 0<P.height j ∧ P.height j<A ∧ A≤1
  phase_a : a=Real.cos δ • P.e 0+Real.sin δ • P.e 1
  phase_b : b=Real.cos δ • P.e 1-Real.sin δ • P.e 0
  rho_eq : ∀ φ, P.rho j φ=exitRadius A (P.height j) (φ-δ)
  point_eq : ∀ φ, polar P.e (P.rho j φ) φ=capExitPoint (P.e 2) a b A (P.height j) (φ-δ)
