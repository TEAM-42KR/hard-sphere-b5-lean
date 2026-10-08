import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom
open scoped RealInnerProductSpace

def SolidGeom.CapPolar.polar (e : Fin 3 → E3) (t φ : ℝ) : E3 :=
  (Real.sin t*Real.cos φ) • e 0+(Real.sin t*Real.sin φ) • e 1+Real.cos t • e 2

structure SolidGeom.CapPolar.Profile where
  e : Fin 3 → E3
  frame : Orthonormal ℝ e
  normal : Fin 3 → E3
  normal_unit : ∀ j, ‖normal j‖ = 1
  height : Fin 3 → ℝ
  height_pos : ∀ j, 0 < height j
  pole_inside : ∀ j, height j < inner ℝ (normal j) (e 2)
  rho : Fin 3 → ℝ → ℝ
  rho_continuous : ∀ j, Continuous (rho j)
  rho_range : ∀ j φ, 0 < rho j φ ∧ rho j φ < Real.pi
  ray_boundary : ∀ j φ,
    inner ℝ (normal j) (SolidGeom.CapPolar.polar e (rho j φ) φ) = height j

def SolidGeom.CapPolar.caps (P : SolidGeom.CapPolar.Profile) : Set E3 :=
  {u | ‖u‖ = 1 ∧ ∀ j, P.height j ≤ inner ℝ (P.normal j) u}

def SolidGeom.CapPolar.winner (P : SolidGeom.CapPolar.Profile) (φ : ℝ) : Fin 3 :=
  if P.rho 0 φ ≤ P.rho 1 φ ∧ P.rho 0 φ ≤ P.rho 2 φ then 0
    else if P.rho 1 φ ≤ P.rho 2 φ then 1 else 2

def SolidGeom.CapPolar.radius (P : SolidGeom.CapPolar.Profile) (φ : ℝ) : ℝ :=
  P.rho (SolidGeom.CapPolar.winner P φ) φ

def SolidGeom.CapPolar.sector (P : SolidGeom.CapPolar.Profile) (j : Fin 3) : Set ℝ :=
  Set.Icc 0 (2*Real.pi) ∩ {φ | SolidGeom.CapPolar.winner P φ = j}

def SolidGeom.CapPolar.tangent (P : SolidGeom.CapPolar.Profile) (φ : ℝ) : E3 :=
  Real.cos φ • P.e 0+Real.sin φ • P.e 1

def SolidGeom.CapPolar.momentDensity (P : SolidGeom.CapPolar.Profile) (j : Fin 3) (φ : ℝ) : E3 :=
  ((P.rho j φ-Real.sin (P.rho j φ)*Real.cos (P.rho j φ))/2) •
    SolidGeom.CapPolar.tangent P φ+
  ((Real.sin (P.rho j φ))^2/2) • P.e 2

#print axioms SolidGeom.CapPolar.Profile
