import Mathlib
set_option autoImplicit false
open scoped Classical
noncomputable section
theorem proof_SphereGeom_Aux_Crofton_encard_monotone_iUnion {α : Type} (s : ℕ → Set α) (hs : Monotone s) :
    (⋃ n, s n).encard = ⨆ n, (s n).encard := by
  classical
  apply le_antisymm
  · by_cases ht : (⨆ n, (s n).encard) = ⊤
    · rw [ht]; exact le_top
    · by_contra h
      have hlt : (⨆ n, (s n).encard) < (⋃ n, s n).encard := lt_of_not_ge h
      let m := (⨆ n, (s n).encard).toNat
      have hm : (m : ℕ∞) = ⨆ n, (s n).encard := ENat.natCast_toNat ht
      have hsize : ((m + 1 : ℕ) : ℕ∞) ≤ (⋃ n, s n).encard := by
        rw [Nat.cast_add, Nat.cast_one, ENat.natCast_add_one_le_iff, hm]
        exact hlt
      obtain ⟨t, htU, htcard⟩ := Set.exists_subset_encard_eq hsize
      have htfin : t.Finite := Set.encard_lt_top_iff.mp (by rw [htcard]; exact ENat.natCast_lt_top _)
      obtain ⟨I, hI, htI⟩ := Set.finite_subset_iUnion htfin htU
      let J := hI.toFinset
      have htmax : t ⊆ s (J.sup id) := by
        intro x hx
        rcases Set.mem_iUnion.mp (htI hx) with ⟨j, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hj, hxj⟩
        exact hs (Finset.le_sup (f := id) (hI.mem_toFinset.mpr hj)) hxj
      have hh : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
        rw [← htcard]
        exact (Set.encard_mono htmax).trans (hm ▸ le_iSup (fun n => (s n).encard) (J.sup id))
      exact (Nat.not_succ_le_self m) (by exact_mod_cast hh)
  · exact iSup_le fun n => Set.encard_mono (Set.subset_iUnion s n)
