import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_tailAngle
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped RealInnerProductSpace

private lemma CG_cross_smul_left (a : ℝ) (v w : E3) :
    SphereGeom.cross (a • v) w=a • SphereGeom.cross v w := by
  ext k
  fin_cases k <;> simp [SphereGeom.cross,crossProduct,PiLp.smul_apply] <;> ring
private lemma CG_cross_smul_right (a : ℝ) (v w : E3) :
    SphereGeom.cross v (a • w)=a • SphereGeom.cross v w := by
  ext k
  fin_cases k <;> simp [SphereGeom.cross,crossProduct,PiLp.smul_apply] <;> ring

theorem proof_SolidGeom_CapPolar_capCorner_pos_smul (u n m : E3) (r s : ℝ)
    (hr : 0<r) (hs : 0<s) : capCorner u (r • n) (s • m)=capCorner u n m := by
  unfold capCorner
  rw [CG_cross_smul_left,CG_cross_smul_left,CG_cross_smul_left,CG_cross_smul_right]
  simp only [real_inner_smul_left,real_inner_smul_right]
  let z : ℂ := ⟨inner ℝ (SphereGeom.cross n u) (SphereGeom.cross m u),
    inner ℝ u (SphereGeom.cross (SphereGeom.cross n u) (SphereGeom.cross m u))⟩
  have hz : (⟨s*(r*inner ℝ (SphereGeom.cross n u) (SphereGeom.cross m u)),
      r*(s*inner ℝ u (SphereGeom.cross (SphereGeom.cross n u) (SphereGeom.cross m u)))⟩ : ℂ)=
        ((r*s:ℝ):ℂ)*z := by
    apply Complex.ext <;> simp [z] <;> ring
  rw [hz]
  exact Complex.arg_real_mul z (mul_pos hr hs)

#print axioms proof_SolidGeom_CapPolar_capCorner_pos_smul
