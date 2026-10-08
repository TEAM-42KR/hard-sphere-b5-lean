import Mathlib
set_option autoImplicit false

open Set

theorem proof_SphereGeom_Aux_Arrangement_finite_nonnegative_intervals (k : ℕ) (f : Fin k → ℝ → ℝ) (p q : ℝ)
    (hpq : p ≤ q) (hf : ∀ i, Continuous (f i))
    (hz : ∀ i, ({t : ℝ | t ∈ Icc p q ∧ f i t = 0}.Finite ∨ ∀ t, f i t = 0)) :
    ∃ (M : ℕ) (a b : Fin M → ℝ) (F : Set ℝ),
      F.Finite ∧ (∀ m, a m < b m) ∧
      {t : ℝ | t ∈ Icc p q ∧ ∀ i, 0 ≤ f i t} = (⋃ m, Icc (a m) (b m)) ∪ F := by
  classical
  let Z : Fin k → Set ℝ := fun i =>
    if (∀ t, f i t = 0) then ∅ else {t : ℝ | t ∈ Icc p q ∧ f i t = 0}
  have hZ : ∀ i, (Z i).Finite := by
    intro i
    dsimp [Z]
    split_ifs with hi
    · exact finite_empty
    · exact (hz i).resolve_right hi
  let E : Set ℝ := {p, q} ∪ ⋃ i, Z i
  have hE : E.Finite := ((finite_singleton q).insert p).union (finite_iUnion hZ)
  have hpE : p ∈ E := by simp [E]
  have hqE : q ∈ E := by simp [E]
  let S : Set ℝ := {t : ℝ | t ∈ Icc p q ∧ ∀ i, 0 ≤ f i t}
  have hSclosed : IsClosed S := by
    have hS : S = Icc p q ∩ ⋂ i, {t : ℝ | 0 ≤ f i t} := by
      ext x
      simp only [S, mem_setOf_eq, mem_inter_iff, mem_iInter]
    rw [hS]
    exact isClosed_Icc.inter (isClosed_iInter fun i => isClosed_le continuous_const (hf i))
  have hcover : ∀ t ∈ S, t ∉ E →
      ∃ a b : ℝ, a ∈ E ∧ b ∈ E ∧ a < t ∧ t < b ∧ Icc a b ⊆ S := by
    intro t ht htE
    have hpt : p < t := by
      have hpne : p ≠ t := by
        intro he
        exact htE (he ▸ hpE)
      exact lt_of_le_of_ne ht.1.1 hpne
    have htq : t < q := by
      have hqne : t ≠ q := by
        intro he
        exact htE (he.symm ▸ hqE)
      exact lt_of_le_of_ne ht.1.2 hqne
    obtain ⟨a, ha, hamax⟩ := Set.exists_max_image (E ∩ Iio t) id
      (hE.subset inter_subset_left) ⟨p, hpE, hpt⟩
    obtain ⟨b, hb, hbmin⟩ := Set.exists_min_image (E ∩ Ioi t) id
      (hE.subset inter_subset_left) ⟨q, hqE, htq⟩
    have hat : a < t := ha.2
    have htb : t < b := hb.2
    have hab : a < b := lt_trans hat htb
    have hpa : p ≤ a := hamax p ⟨hpE, hpt⟩
    have hbq : b ≤ q := hbmin q ⟨hqE, htq⟩
    have hnoE : ∀ y ∈ Ioo a b, y ∉ E := by
      intro y hy hyE
      rcases lt_trichotomy y t with hyt | rfl | hty
      · have hya : y ≤ a := hamax y ⟨hyE, hyt⟩
        linarith [hy.1]
      · exact htE hyE
      · have hby : b ≤ y := hbmin y ⟨hyE, hty⟩
        linarith [hy.2]
    have hnozero : ∀ i, ¬(∀ x, f i x = 0) → ∀ y ∈ Ioo a b, f i y ≠ 0 := by
      intro i hi y hy hy0
      apply hnoE y hy
      apply Or.inr
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      have hyIcc : y ∈ Icc p q := ⟨le_trans hpa hy.1.le, le_trans hy.2.le hbq⟩
      change y ∈ Z i
      dsimp [Z]
      rw [if_neg hi]
      exact ⟨hyIcc, hy0⟩
    have hopen : Ioo a b ⊆ S := by
      intro x hx
      refine ⟨⟨le_trans hpa hx.1.le, le_trans hx.2.le hbq⟩, ?_⟩
      intro i
      by_cases hi : ∀ y, f i y = 0
      · simp [hi x]
      · by_contra hn
        have hxneg : f i x < 0 := lt_of_not_ge hn
        by_cases hxt : x ≤ t
        · obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hxt (hf i).continuousOn
            (show (0 : ℝ) ∈ Icc (f i x) (f i t) from ⟨hxneg.le, ht.2 i⟩)
          have hyab : y ∈ Ioo a b := by constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
          exact hnozero i hi y hyab hy0
        · have htx : t ≤ x := le_of_not_ge hxt
          obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' htx (hf i).continuousOn
            (show (0 : ℝ) ∈ Icc (f i x) (f i t) from ⟨hxneg.le, ht.2 i⟩)
          have hyab : y ∈ Ioo a b := by constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
          exact hnozero i hi y hyab hy0
    have hclosed : Icc a b ⊆ S := by
      rw [← closure_Ioo hab.ne]
      exact closure_minimal hopen hSclosed
    exact ⟨a, b, ha.1, hb.1, hat, htb, hclosed⟩
  let C : Set (ℝ × ℝ) := {ab | ab.1 ∈ E ∧ ab.2 ∈ E ∧ ab.1 < ab.2 ∧ Icc ab.1 ab.2 ⊆ S}
  have hC : C.Finite := (hE.prod hE).subset (fun ab hab => ⟨hab.1, hab.2.1⟩)
  letI : Fintype C := hC.fintype
  let e : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  refine ⟨Fintype.card C, (fun m => (e m).val.1), (fun m => (e m).val.2), S ∩ E,
    hE.subset inter_subset_right, (fun m => (e m).property.2.2.1), ?_⟩
  change S = (⋃ m, Icc (e m).val.1 (e m).val.2) ∪ (S ∩ E)
  ext t
  constructor
  · intro ht
    by_cases htE : t ∈ E
    · exact Or.inr ⟨ht, htE⟩
    · obtain ⟨a, b, haE, hbE, hat, htb, hsub⟩ := hcover t ht htE
      let c : C := ⟨(a, b), haE, hbE, lt_trans hat htb, hsub⟩
      refine Or.inl (mem_iUnion.mpr ⟨e.symm c, ?_⟩)
      simpa [c] using (show t ∈ Icc a b from ⟨hat.le, htb.le⟩)
  · rintro (ht | ht)
    · obtain ⟨m, hm⟩ := mem_iUnion.mp ht
      exact (e m).property.2.2.2 hm
    · exact ht.1
