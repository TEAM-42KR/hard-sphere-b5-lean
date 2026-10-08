import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_AlignedCap
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_sector_area_primitive
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_sector_moment_primitive
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_radial_moment_integral
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
set_option maxHeartbeats 1400000
private lemma SolidGeom.CapPolar.AI_direction (P : Profile) (j : Fin 3) (C : AlignedCap P j) (φ : ℝ) :
    capDirection C.a C.b (φ-C.δ)=tangent P φ := by
  unfold capDirection tangent
  rw [C.phase_a,C.phase_b]
  ext k
  simp [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,Real.cos_sub,Real.sin_sub]
  nlinarith [congrArg (fun z : ℝ => P.e 0 k*Real.cos φ*z) (Real.sin_sq_add_cos_sq C.δ),
    congrArg (fun z : ℝ => P.e 1 k*Real.sin φ*z) (Real.sin_sq_add_cos_sq C.δ)]
private lemma SolidGeom.CapPolar.AI_moment_radial (P : Profile) (j : Fin 3) (C : AlignedCap P j) (φ : ℝ) :
    momentDensity P j φ=∫ρ in (0)..exitRadius C.A (P.height j) (φ-C.δ),
      Real.sin ρ • polarRay (P.e 2) C.a C.b (φ-C.δ) ρ := by
  rw [radial_moment_integral,AI_direction]
  unfold momentDensity
  rw [C.rho_eq]
theorem proof_SolidGeom_CapPolar_aligned_moment_integral (P : SolidGeom.CapPolar.Profile)
    (j : Fin 3) (C : SolidGeom.CapPolar.AlignedCap P j) (a b : ℝ) :
    (∫ φ in a..b, SolidGeom.CapPolar.momentDensity P j φ)=
      SolidGeom.CapPolar.momentPrimitive (P.e 2) C.a C.b C.A (P.height j) (b-C.δ)-
        SolidGeom.CapPolar.momentPrimitive (P.e 2) C.a C.b C.A (P.height j) (a-C.δ)  := by
  calc
    _ = ∫φ in a..b, ∫ρ in (0)..exitRadius C.A (P.height j) (φ-C.δ),
        Real.sin ρ • polarRay (P.e 2) C.a C.b (φ-C.δ) ρ := by
      apply intervalIntegral.integral_congr
      intro φ _
      exact AI_moment_radial P j C φ
    _ = ∫ψ in (a-C.δ)..(b-C.δ), ∫ρ in (0)..exitRadius C.A (P.height j) ψ,
        Real.sin ρ • polarRay (P.e 2) C.a C.b ψ ρ :=
      intervalIntegral.integral_comp_sub_right
        (fun ψ : ℝ => ∫ρ in (0)..exitRadius C.A (P.height j) ψ, Real.sin ρ • polarRay (P.e 2) C.a C.b ψ ρ) C.δ
    _ = _ := sector_moment_primitive _ _ _ _ _ _ _ C.bounds.1 C.bounds.2.1 C.bounds.2.2 C.frame
#print axioms proof_SolidGeom_CapPolar_aligned_moment_integral
