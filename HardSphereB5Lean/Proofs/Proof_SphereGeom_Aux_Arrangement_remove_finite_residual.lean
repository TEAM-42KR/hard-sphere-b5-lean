import Mathlib
set_option autoImplicit false

open Set

theorem proof_SphereGeom_Aux_Arrangement_remove_finite_residual (X : Type*) [MetricSpace X] (A F B : Set X)
    (hA : IsClosed A) (hF : F.Finite) (hB : B = A ∪ F)
    (hacc : ∀ u ∈ B, ∀ ε : ℝ, 0 < ε → ∃ v ∈ B, v ≠ u ∧ dist v u < ε) :
    B = A := by
  classical
  apply subset_antisymm
  · intro u hu
    by_contra huA
    have hclosed : IsClosed (A ∪ (F \ {u})) := hA.union (hF.subset sdiff_subset).isClosed
    have huO : u ∈ (A ∪ (F \ {u}))ᶜ := by simp [huA]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl u huO
    obtain ⟨v, hvB, hvu, hvdist⟩ := hacc u hu ε hε
    have hvO : v ∈ (A ∪ (F \ {u}))ᶜ := hball (Metric.mem_ball.mpr hvdist)
    have hvUnion : v ∈ A ∪ F := hB ▸ hvB
    apply hvO
    rcases hvUnion with hvA | hvF
    · exact Or.inl hvA
    · exact Or.inr ⟨hvF, by simpa only [mem_singleton_iff] using hvu⟩
  · intro u hu
    rw [hB]
    exact Or.inl hu
