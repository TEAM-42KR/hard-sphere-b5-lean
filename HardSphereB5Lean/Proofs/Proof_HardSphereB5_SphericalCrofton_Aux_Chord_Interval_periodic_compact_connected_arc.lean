import Mathlib
set_option autoImplicit false
open MeasureTheory Real
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_periodic_compact_connected_arc {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : ℝ → X) (hC : Continuous C) (T : ℝ) (hT : 0 < T)
    (hper : Function.Periodic C T)
    (hinj : ∀ a b : ℝ, b - a < T → Set.InjOn C (Set.Icc a b))
    (S : Set X) (hS : IsConnected S) (hcompact : IsCompact S)
    (hsub : S ⊆ Set.range C) (cut : ℝ) (hcut : C cut ∉ S) :
    ∃ a b : ℝ, a ≤ b ∧ b - a < T ∧ S = C '' Set.Icc a b := by
  letI : Fact (0 < T) := ⟨hT⟩
  have himg : C '' Set.Icc cut (cut + T) = Set.range C := by
    apply Set.Subset.antisymm (Set.image_subset_range _ _)
    rintro x ⟨t, rfl⟩
    have hx : (t : AddCircle T) ∈ ((↑) : ℝ → AddCircle T) '' Set.Icc cut (cut + T) := by
      rw [AddCircle.coe_image_Icc_eq T cut]
      trivial
    obtain ⟨s, hs, hst⟩ := hx
    refine ⟨s, hs, ?_⟩
    simpa only [Function.Periodic.lift_coe] using congrArg hper.lift hst
  let U : Set ℝ := Set.Icc cut (cut + T) ∩ C ⁻¹' S
  have hU : IsCompact U :=
    isCompact_Icc.inter_right (hcompact.isClosed.preimage hC)
  have hUimg : C '' U = S := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, ht, rfl⟩
      exact ht.2
    · intro x hx
      obtain ⟨t, ht, htx⟩ := himg.symm ▸ hsub hx
      exact ⟨t, ⟨ht, (show C t ∈ S by simpa only [htx] using hx)⟩, htx⟩
  have hUne : U.Nonempty := by
    obtain ⟨x, hx⟩ := hS.nonempty
    obtain ⟨t, ht, _⟩ := hUimg.symm ▸ hx
    exact ⟨t, ht⟩
  have hUstrict (t : ℝ) (ht : t ∈ U) : cut < t ∧ t < cut + T := by
    obtain ⟨⟨hlt, htu⟩, hts⟩ := ht
    change C t ∈ S at hts
    refine ⟨lt_of_le_of_ne hlt ?_, lt_of_le_of_ne htu ?_⟩
    · intro heq
      subst t
      exact hcut hts
    · intro heq
      subst t
      rw [hper cut] at hts
      exact hcut hts
  have hUinj : Set.InjOn C U := by
    intro s hs t ht hst
    by_cases hle : s ≤ t
    · exact hinj s t (by
        have h₁ := hUstrict s hs
        have h₂ := hUstrict t ht
        linarith) ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hst
    · have hle' : t ≤ s := le_of_not_ge hle
      exact hinj t s (by
        have h₁ := hUstrict s hs
        have h₂ := hUstrict t ht
        linarith) ⟨hle', le_rfl⟩ ⟨le_rfl, hle'⟩ hst
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let f : U → X := fun t => C t
  have hf : Continuous f := hC.comp continuous_subtype_val
  have hfemb := hf.isClosedEmbedding (fun s t heq => Subtype.ext (hUinj s.property t.property heq))
  have hfimg : f '' Set.univ = S := by
    change (C ∘ (Subtype.val : U → ℝ)) '' Set.univ = S
    rw [Set.image_comp, Set.image_univ, Subtype.range_val]
    exact hUimg
  have hUpcsub : IsPreconnected (Set.univ : Set U) :=
    hfemb.isInducing.isPreconnected_image.mp (hfimg ▸ hS.isPreconnected)
  have hUpc : IsPreconnected U := by
    have hh := Topology.IsInducing.subtypeVal.isPreconnected_image.mpr hUpcsub
    simpa only [Set.image_univ, Subtype.range_val] using hh
  have hconn : IsConnected U := ⟨hUne, hUpc⟩
  let a := sInf U
  let b := sSup U
  have ha : a ∈ U := hU.sInf_mem hUne
  have hb : b ∈ U := hU.sSup_mem hUne
  have hle : a ≤ b := csInf_le hU.bddBelow hb
  have hshort : b - a < T := by
    have h₁ := hUstrict a ha
    have h₂ := hUstrict b hb
    linarith
  refine ⟨a, b, hle, hshort, ?_⟩
  rw [← hUimg, eq_Icc_of_connected_compact hconn hU]
