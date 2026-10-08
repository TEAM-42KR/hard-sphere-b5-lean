import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_tailAngle
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped RealInnerProductSpace
private lemma CG_cross_inner (e f v a : E3) :
    inner ℝ (SphereGeom.cross e f) (SphereGeom.cross v a) =
      inner ℝ e v * inner ℝ f a - inner ℝ e a * inner ℝ f v := by
  simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,Fin.sum_univ_succ]
  ring

private lemma CG_q_inner (c : Fin 4 → Pt) (i j : Fin 4) :
    q c i j = inner ℝ (c j - c i) (c j - c i) := by
  rw [real_inner_self_eq_norm_sq]
  simp only [q, dist_eq_norm, norm_sub_rev]

private lemma CG_inner_from_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (c j - c i) (c k - c i) = (q c i j + q c i k - q c j k) / 2 := by
  have h := norm_sub_sq_real (c j - c i) (c k - c i)
  have hv : (c j - c i) - (c k - c i) = c j - c k := by abel
  rw [hv] at h
  simp only [q, dist_eq_norm] at ⊢
  rw [norm_sub_rev (c i) (c j), norm_sub_rev (c i) (c k)]
  linarith

private lemma CG_oriented_tangent_triple (v w u : E3) (hu : inner ℝ u u=1) :
    inner ℝ u (SphereGeom.cross (SphereGeom.cross v u) (SphereGeom.cross w u)) =
      inner ℝ u (SphereGeom.cross v w) := by
  have hi : inner ℝ u (SphereGeom.cross (SphereGeom.cross v u) (SphereGeom.cross w u)) =
      inner ℝ u u*inner ℝ u (SphereGeom.cross v w) := by
    simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_succ]
    ring
  rw [hi,hu,one_mul]

private lemma CG_triple_gram_sq (v w u : E3) :
    (inner ℝ u (SphereGeom.cross v w))^2 =
      (inner ℝ v v*inner ℝ w w-(inner ℝ v w)^2)*inner ℝ u u -
        inner ℝ v v*(inner ℝ w u)^2-inner ℝ w w*(inner ℝ v u)^2+
        2*inner ℝ v w*inner ℝ v u*inner ℝ w u := by
  simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  ring

private theorem CG_corner_arg_of_sphere_gram (v w u : E3) (a b c : ℝ)
    (hu : inner ℝ u u=1) (hv : inner ℝ v v=a) (hw : inner ℝ w w=b)
    (hvw : inner ℝ v w=(a+b-c)/2)
    (hvu : inner ℝ v u=a/2) (hwu : inner ℝ w u=b/2)
    (hpos : 0 < inner ℝ u (SphereGeom.cross v w)) :
    Complex.arg ⟨inner ℝ (SphereGeom.cross v u) (SphereGeom.cross w u),
      inner ℝ u (SphereGeom.cross (SphereGeom.cross v u) (SphereGeom.cross w u))⟩ =
      atan2 (2*Real.sqrt (QT a b c)) (2*(a+b-c)-a*b) := by
  have hr : inner ℝ (SphereGeom.cross v u) (SphereGeom.cross w u) =
      (2*(a+b-c)-a*b)/4 := by
    rw [CG_cross_inner,hvw,hvu,show inner ℝ u w=b/2 from (real_inner_comm w u).trans hwu,hu]
    ring
  have hg := CG_triple_gram_sq v w u
  rw [hu,hv,hw,hvw,hvu,hwu] at hg
  have hq : QT a b c = (2*inner ℝ u (SphereGeom.cross v w))^2 := by
    unfold QT DeltaT
    nlinarith [hg]
  have hs : Real.sqrt (QT a b c)=2*inner ℝ u (SphereGeom.cross v w) := by
    rw [hq,Real.sqrt_sq_eq_abs,abs_of_pos (mul_pos (by norm_num) hpos)]
  rw [hr,CG_oriented_tangent_triple v w u hu]
  have he : (4 : ℂ)*⟨(2*(a+b-c)-a*b)/4,inner ℝ u (SphereGeom.cross v w)⟩ =
      ⟨2*(a+b-c)-a*b,2*Real.sqrt (QT a b c)⟩ := by
    rw [hs]
    apply Complex.ext <;> simp <;> ring
  unfold atan2
  rw [← he]
  simpa only [Complex.ofReal_ofNat] using
    (Complex.arg_real_mul (⟨(2*(a+b-c)-a*b)/4,inner ℝ u (SphereGeom.cross v w)⟩ : ℂ)
      (by norm_num : (0:ℝ)<4)).symm

private lemma CG_inner_two_spheres (u v : E3) (hu : ‖u‖=1) (hv : ‖u-v‖=1) :
    inner ℝ v u=inner ℝ v v/2 := by
  have hs := norm_sub_sq_real u v
  rw [hu,hv] at hs
  have hc : inner ℝ v u=inner ℝ u v := real_inner_comm _ _
  have hh : inner ℝ v v=‖v‖^2 := real_inner_self_eq_norm_sq _
  nlinarith

theorem proof_SolidGeom_CapPolar_capCorner_gamma (c : Fin 4 → E3) (i j k : Fin 4)
    (u : E3) (hu : ‖u‖=1) (hj : ‖u-(c j-c i)‖=1) (hk : ‖u-(c k-c i)‖=1)
    (hpos : 0 < inner ℝ u (SphereGeom.cross (c j-c i) (c k-c i))) :
    capCorner u (c j-c i) (c k-c i)=gammaA c i j k := by
  unfold capCorner gammaA Qf
  exact CG_corner_arg_of_sphere_gram (c j-c i) (c k-c i) u _ _ _
    (by rw [real_inner_self_eq_norm_sq,hu];norm_num)
    (CG_q_inner c i j).symm (CG_q_inner c i k).symm
    (CG_inner_from_q c i j k)
    (by rw [CG_q_inner];exact CG_inner_two_spheres u _ hu hj)
    (by rw [CG_q_inner];exact CG_inner_two_spheres u _ hu hk) hpos

#print axioms proof_SolidGeom_CapPolar_capCorner_gamma
