import HardSphereB5Lean.Definitions.Def_SphereGeom_fixedZFrame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_lintegral_encard_with_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_fixedZFrame_oriented_orthonormal
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_fixedZFrame_curve_contDiffAt
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_fixedZFrame_measurable
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_fixedZ_bad_parameters_finite
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_ae_encard_image_diff_countable
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_deriv_tangent_sphere_Ioo
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_measurable_encard_greatCircle_sigmaCompact
set_option autoImplicit false
open MeasureTheory SphereGeom

set_option backward.isDefEq.respectTransparency false in
theorem proof_SphereGeom_Aux_Crofton_lintegral_encard_greatCircle_sigmaCompact (γ : ℝ → E3) (a b : ℝ)
    (hγ : ContDiff ℝ 1 γ) (hs : ∀ t ∈ Set.Icc a b, ‖γ t‖ = 1)
    (hreg : ∀ t ∈ Set.Icc a b, deriv γ t ≠ 0) (hinj : Set.InjOn γ (Set.Icc a b))
    (S : Set ℝ) (hS : MeasurableSet S) (hSab : S ⊆ Set.Icc a b) (hSc : IsSigmaCompact S) :
    ∫⁻ p, ((greatCircle p ∩ γ '' S).encard : ENNReal) ∂dOmega =
      4 * ∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖ := by
  classical
  let Q : ℝ → ℝ := fun s => (γ s) 0 ^ 2 + (γ s) 1 ^ 2
  let U : Set ℝ := Set.Ioo a b ∩ {s | Q s ≠ 0}
  let B : Set ℝ := {s | s ∈ Set.Icc a b ∧ Q s = 0}
  let T : Set ℝ := ({a, b} : Set ℝ) ∪ B
  let V : Set ℝ := S \ T
  let A : ℝ → E3 := fun s => fixedZA (γ s)
  let C : ℝ → E3 := fun s => fixedZB (γ s)
  have hQ : Continuous Q := by dsimp [Q]; fun_prop
  have hU : IsOpen U := isOpen_Ioo.inter
    ((isClosed_singleton.preimage hQ).isOpen_compl)
  have hB : B.Finite := SphereGeom.Aux.Crofton.fixedZ_bad_parameters_finite γ a b hs hinj
  have hT : T.Finite := (Set.toFinite ({a, b} : Set ℝ)).union hB
  have hVm : MeasurableSet V := hS.diff hT.measurableSet
  have hVU : V = S ∩ U := by
    ext s
    simp only [V, U, T, B, Set.mem_diff, Set.mem_inter_iff,
      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Set.mem_Ioo, Set.mem_Icc]
    constructor
    · rintro ⟨hss, hst⟩
      have hi := hSab hss
      have hsa : s ≠ a := fun h => hst (Or.inl (Or.inl h))
      have hsb : s ≠ b := fun h => hst (Or.inl (Or.inr h))
      have hn : Q s ≠ 0 := fun h => hst (Or.inr ⟨hi, h⟩)
      exact ⟨hss, ⟨lt_of_le_of_ne hi.1 hsa.symm, lt_of_le_of_ne hi.2 hsb⟩, hn⟩
    · rintro ⟨hss, ⟨hsa, hsb⟩, hq⟩
      refine ⟨hss, ?_⟩
      rintro (h | ⟨hi, hz⟩)
      · rcases h with h | h
        · exact hsa.ne' h
        · exact hsb.ne h
      · exact hq hz
  have hVsub : V ⊆ S := Set.diff_subset
  have hVUsub : V ⊆ U := by rw [hVU]; exact Set.inter_subset_right
  have hVSc : IsSigmaCompact V := by
    haveI : LocallyCompactSpace U := hU.locallyCompactSpace
    have hUc : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
    obtain ⟨K, hK, hKu⟩ := hSc
    obtain ⟨L, hL, hLu⟩ := hUc
    have he : V = ⋃ n : ℕ × ℕ, K n.1 ∩ L n.2 := by
      rw [hVU, ← hKu, ← hLu]
      ext s
      simp only [Set.mem_inter_iff, Set.mem_iUnion]
      constructor
      · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; exact ⟨(i,j), hi, hj⟩
      · rintro ⟨⟨i,j⟩, hi, hj⟩; exact ⟨⟨i,hi⟩, ⟨j,hj⟩⟩
    rw [he]
    exact isSigmaCompact_iUnion_of_isCompact _ (fun n => (hK n.1).inter (hL n.2))
  have hframe : ∀ s ∈ V, Orthonormal ℝ ![A s, C s, γ s] ∧ cross (A s) (C s) = γ s := by
    intro s hss
    exact SphereGeom.Aux.Crofton.fixedZFrame_oriented_orthonormal (γ s)
      (hs s (hSab (hVsub hss))) (hVUsub hss).2
  have hda : ∀ s ∈ V, DifferentiableAt ℝ A s := by
    intro s hss
    exact (SphereGeom.Aux.Crofton.fixedZFrame_curve_contDiffAt γ hγ s (hVUsub hss).2).1.differentiableAt (by norm_num)
  have hdc : ∀ s ∈ V, DifferentiableAt ℝ C s := by
    intro s hss
    exact (SphereGeom.Aux.Crofton.fixedZFrame_curve_contDiffAt γ hγ s (hVUsub hss).2).2.differentiableAt (by norm_num)
  have hdγ : ∀ s ∈ V, DifferentiableAt ℝ γ s := fun s _ => hγ.differentiable (by norm_num) s
  have hoa : ∀ s ∈ V, (fun t => inner ℝ (A t) (γ t)) =ᶠ[nhds s] (fun _ => 0) := by
    intro s hss
    filter_upwards [hU.mem_nhds (hVUsub hss)] with t ht
    have hon := (SphereGeom.Aux.Crofton.fixedZFrame_oriented_orthonormal (γ t)
      (hs t (Set.Ioo_subset_Icc_self ht.1)) ht.2).1
    simpa [A] using (orthonormal_iff_ite.mp hon) (0 : Fin 3) 2
  have hoc : ∀ s ∈ V, (fun t => inner ℝ (C t) (γ t)) =ᶠ[nhds s] (fun _ => 0) := by
    intro s hss
    filter_upwards [hU.mem_nhds (hVUsub hss)] with t ht
    have hon := (SphereGeom.Aux.Crofton.fixedZFrame_oriented_orthonormal (γ t)
      (hs t (Set.Ioo_subset_Icc_self ht.1)) ht.2).1
    simpa [C] using (orthonormal_iff_ite.mp hon) (1 : Fin 3) 2
  have htan : ∀ s ∈ V, inner ℝ (deriv γ s) (γ s) = 0 := by
    intro s hss
    exact SphereGeom.Aux.Crofton.deriv_tangent_sphere_Ioo γ a b s hs (hdγ s hss) (hVUsub hss).1
  have hlocal : (∫⁻ p, ((greatCircle p ∩ γ '' V).encard : ENNReal) ∂dOmega) =
      4 * ∫⁻ t in V, ENNReal.ofReal ‖deriv γ t‖ :=
    SphereGeom.Aux.Crofton.lintegral_encard_with_frame γ A C V hVm
      (SphereGeom.Aux.Crofton.fixedZFrame_measurable.2.1.comp hγ.continuous.measurable)
      (SphereGeom.Aux.Crofton.fixedZFrame_measurable.2.2.comp hγ.continuous.measurable)
      hγ.continuous.measurable (fun s hss => hs s (hSab (hVsub hss)))
      (hinj.mono (hVsub.trans hSab)) hframe hda hdc hdγ hoa hoc htan
      (SphereGeom.Aux.Crofton.measurable_encard_greatCircle_sigmaCompact (γ '' V)
        (hVSc.image hγ.continuous))
  have hcount := SphereGeom.Aux.Crofton.ae_encard_image_diff_countable γ S T hT.countable
    (fun s hss => hs s (hSab hss))
  have hset : V =ᵐ[volume] S := by
    filter_upwards [hT.countable.ae_notMem (volume : Measure ℝ)] with s hst
    change (s ∈ S ∧ s ∉ T) = (s ∈ S)
    simp only [hst, not_false_eq_true, and_true]
  rw [← lintegral_congr_ae hcount, hlocal, setLIntegral_congr hset]
