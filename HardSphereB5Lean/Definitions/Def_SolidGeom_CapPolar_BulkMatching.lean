import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_Profile
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped RealInnerProductSpace

structure SolidGeom.CapPolar.BulkMatching (P : SolidGeom.CapPolar.Profile)
    (c : Fin 4 → E3) (i : Fin 4) (o : Fin 3 → Fin 4) : Prop where
  label_ne : ∀ j, o j ≠ i
  label_injective : Function.Injective o
  normal_eq : ∀ j, P.normal j = (dist (c i) (c (o j)))⁻¹ • (c (o j)-c i)
  height_eq : ∀ j, P.height j = dist (c i) (c (o j))/2

def SolidGeom.CapPolar.exitPoint (P : SolidGeom.CapPolar.Profile) (φ : ℝ) : E3 :=
  SolidGeom.CapPolar.polar P.e (SolidGeom.CapPolar.radius P φ) φ

def SolidGeom.CapPolar.activeAzimuth (P : SolidGeom.CapPolar.Profile) (j : Fin 3) : Set ℝ :=
  Set.Icc 0 (2*Real.pi) ∩ {φ | P.rho j φ = SolidGeom.CapPolar.radius P φ}

def SolidGeom.CapPolar.tieAzimuth (P : SolidGeom.CapPolar.Profile) : Set ℝ :=
  Set.Icc 0 (2*Real.pi) ∩ {φ | ∃ j k : Fin 3, j ≠ k ∧
    P.rho j φ = SolidGeom.CapPolar.radius P φ ∧ P.rho k φ = SolidGeom.CapPolar.radius P φ}

def SolidGeom.CapPolar.angularCell (cuts : Finset ℝ) (a b : ℝ) : Set ℝ := Set.Ioo a b

#print axioms SolidGeom.CapPolar.BulkMatching
