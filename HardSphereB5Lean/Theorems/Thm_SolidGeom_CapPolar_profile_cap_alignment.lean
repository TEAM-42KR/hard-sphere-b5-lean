import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_profile_cap_alignment
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_Profile
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar

theorem SolidGeom.CapPolar.profile_cap_alignment :
    ∀ (P : SolidGeom.CapPolar.Profile)
    (hor : SphereGeom.cross (P.e 2) (P.e 0)=P.e 1) (j : Fin 3), ∃ (a b : SphereGeom.E3) (δ : ℝ),
      Orthonormal ℝ (fun k : Fin 3 => ![P.e 2,a,b] k) ∧
      SphereGeom.cross (P.e 2) a=b ∧
      P.normal j=SolidGeom.CapPolar.capAxis (P.e 2) a (inner ℝ (P.normal j) (P.e 2)) ∧
      0 < P.height j ∧ P.height j < inner ℝ (P.normal j) (P.e 2) ∧
      inner ℝ (P.normal j) (P.e 2)≤1 ∧
      a=Real.cos δ • P.e 0+Real.sin δ • P.e 1 ∧
      b=Real.cos δ • P.e 1-Real.sin δ • P.e 0 ∧
      ∀ φ : ℝ,
        P.rho j φ=SolidGeom.CapPolar.exitRadius (inner ℝ (P.normal j) (P.e 2)) (P.height j) (φ-δ) ∧
        SolidGeom.CapPolar.polar P.e (P.rho j φ) φ=
          SolidGeom.CapPolar.capExitPoint (P.e 2) a b (inner ℝ (P.normal j) (P.e 2)) (P.height j) (φ-δ) :=
  @proof_SolidGeom_CapPolar_profile_cap_alignment
