import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_profile_of_unit
set_option autoImplicit false
noncomputable section
open SphereGeom SolidGeom.CapPolar
open scoped RealInnerProductSpace
set_option maxHeartbeats 1200000
private lemma A4_cross_orthogonal_left (p a : E3) : inner ℝ p (SphereGeom.cross p a)=0 := by
  simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,Fin.sum_univ_succ]
  ring
private lemma A4_cross_orthogonal_right (p a : E3) : inner ℝ a (SphereGeom.cross p a)=0 := by
  simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,Fin.sum_univ_succ]
  ring
private lemma A4_cross_norm (p a : E3) :
    inner ℝ (SphereGeom.cross p a) (SphereGeom.cross p a)=
      inner ℝ p p*inner ℝ a a-(inner ℝ p a)^2 := by
  simp [SphereGeom.cross,crossProduct,PiLp.inner_apply,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  ring

theorem proof_SolidGeom_CapPolar_profile_of_unit_oriented
    (p : SphereGeom.E3) (hp : ‖p‖ = 1)
    (n : Fin 3 → SphereGeom.E3) (hn : ∀ j, ‖n j‖ = 1) (h : Fin 3 → ℝ)
    (hh : ∀ j, 0 < h j) (hi : ∀ j, h j < inner ℝ (n j) p) :
    ∃ P : SolidGeom.CapPolar.Profile, P.e 2 = p ∧
      SphereGeom.cross (P.e 2) (P.e 0)=P.e 1 ∧ P.normal = n ∧ P.height = h  := by
  obtain ⟨P,hp₂,_,_⟩ := profile_of_unit p hp n hn h hh hi
  let a := P.e 0
  let b := SphereGeom.cross p a
  have hPF := orthonormal_iff_ite.mp P.frame
  have hpp : inner ℝ p p=1 := by rw [real_inner_self_eq_norm_sq,hp]; norm_num
  have haa : inner ℝ a a=1 := by simpa only [a,if_true] using hPF 0 0
  have hpa : inner ℝ p a=0 := by simpa only [hp₂,a,show (2:Fin 3)≠0 by decide,if_false] using hPF 2 0
  have hap : inner ℝ a p=0 := (real_inner_comm p a).trans hpa
  have hpb : inner ℝ p b=0 := A4_cross_orthogonal_left p a
  have hbp : inner ℝ b p=0 := (real_inner_comm p b).trans hpb
  have hab : inner ℝ a b=0 := A4_cross_orthogonal_right p a
  have hba : inner ℝ b a=0 := (real_inner_comm a b).trans hab
  have hbb : inner ℝ b b=1 := by change inner ℝ (SphereGeom.cross p a) (SphereGeom.cross p a)=1;rw [A4_cross_norm,hpp,haa,hpa];norm_num
  let e : Fin 3 → E3 := ![a,b,p]
  have he : Orthonormal ℝ e := by
    apply orthonormal_iff_ite.mpr
    intro j k
    fin_cases j <;> fin_cases k <;> dsimp [e]
    all_goals first | exact haa | exact hbb | exact hpp | exact hpa | exact hap | exact hpb | exact hbp | exact hab | exact hba
  obtain ⟨Q,hQe,hQn,hQh,_⟩ := profile_of_frame e he n hn h hh
    (by intro j;change h j < inner ℝ (n j) p;exact hi j)
  refine ⟨Q,?_,?_,hQn,hQh⟩
  · rw [hQe];rfl
  · rw [hQe];rfl
#print axioms proof_SolidGeom_CapPolar_profile_of_unit_oriented
