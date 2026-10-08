import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_AlignedCap
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_profile_cap_alignment
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar

theorem proof_SolidGeom_CapPolar_alignedCap_exists (P : SolidGeom.CapPolar.Profile)
    (hor : SphereGeom.cross (P.e 2) (P.e 0)=P.e 1) (j : Fin 3) :
    Nonempty (SolidGeom.CapPolar.AlignedCap P j)  := by
  obtain ⟨a,b,δ,hframe,horiented,hnormal,hh,hA,hA1,ha,hb,hroot⟩ :=
    SolidGeom.CapPolar.profile_cap_alignment P hor j
  refine ⟨{
    a := a
    b := b
    A := inner ℝ (P.normal j) (P.e 2)
    δ := δ
    frame := hframe
    oriented := horiented
    normal_eq := hnormal
    pole_cos := rfl
    bounds := ⟨hh,hA,hA1⟩
    phase_a := ha
    phase_b := hb
    rho_eq := fun φ => (hroot φ).1
    point_eq := fun φ => (hroot φ).2
  }⟩
