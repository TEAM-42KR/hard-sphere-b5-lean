import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_profile_of_frame
set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
open SolidGeom.CapPolar SphereGeom
set_option maxHeartbeats 1200000
theorem proof_SolidGeom_CapPolar_profile_of_unit
    (p : SphereGeom.E3) (hp : ‖p‖ = 1)
    (n : Fin 3 → SphereGeom.E3) (hn : ∀ j, ‖n j‖ = 1) (h : Fin 3 → ℝ)
    (hh : ∀ j, 0 < h j) (hi : ∀ j, h j < inner ℝ (n j) p) :
    ∃ P : SolidGeom.CapPolar.Profile, P.e 2 = p ∧ P.normal = n ∧ P.height = h  := by
  have hf : Orthonormal ℝ (({2} : Set (Fin 3)).domRestrict (fun _ => p)) := by
    apply orthonormal_iff_ite.mpr
    intro j k
    have hj : j.val = 2 := by simpa only [Set.mem_singleton_iff] using j.property
    have hk : k.val = 2 := by simpa only [Set.mem_singleton_iff] using k.property
    have hjk : j = k := Subtype.ext (hj.trans hk.symm)
    simp only [hjk,if_true,Set.domRestrict_apply]
    rw [real_inner_self_eq_norm_sq,hp]
    norm_num
  obtain ⟨e,he⟩ := hf.exists_orthonormalBasis_extension_of_card_eq
    (by simp [SphereGeom.E3,finrank_euclideanSpace])
  have he2 : e 2 = p := he 2 (Set.mem_singleton (2 : Fin 3))
  obtain ⟨P,hPe,hPn,hPh,_⟩ := profile_of_frame e e.orthonormal n hn h hh
    (by intro j; simpa only [he2] using hi j)
  refine ⟨P,?_,hPn,hPh⟩
  simpa only [hPe] using he2
#print axioms proof_SolidGeom_CapPolar_profile_of_unit
