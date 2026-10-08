import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_finite_nonnegative_intervals
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_trig_zeros_finite
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_regular_circle_arc
set_option autoImplicit false
open SphereGeom

theorem proof_SphereGeom_Aux_Arrangement_clipped_circle_arcs (k : ℕ) (c e1 e2 n : E3)
    (hframe : Orthonormal ℝ ![e1,e2,n]) (r : ℝ) (hr : 0 < r)
    (α β δ : Fin k → ℝ) :
    let S : Set E3 := circlePt c e1 e2 r ''
      {t ∈ Set.Icc 0 (2 * Real.pi) | ∀ i, 0 ≤ α i * Real.cos t + β i * Real.sin t - δ i}
    ∃ (N : ℕ) (γ : Fin N → ℝ → E3) (F : Set E3),
      F.Finite ∧ (∀ m, ContDiff ℝ 2 (γ m)) ∧
      (∀ m, Set.InjOn (γ m) (Set.Icc 0 1)) ∧
      (∀ m, ∀ t ∈ Set.Icc 0 1, deriv (γ m) t ≠ 0) ∧
      S = (⋃ m, γ m '' Set.Icc 0 1) ∪ F := by
  classical
  let f : Fin k → ℝ → ℝ := fun i t =>
    α i * Real.cos t + β i * Real.sin t - δ i
  let T : Set ℝ := {t ∈ Set.Icc 0 (2 * Real.pi) | ∀ i, 0 ≤ f i t}
  have hf (i : Fin k) : Continuous (f i) := by
    dsimp [f]
    fun_prop
  have hz (i : Fin k) :
      {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ f i t = 0}.Finite ∨
        ∀ t, f i t = 0 := by
    by_cases hzero : α i = 0 ∧ β i = 0 ∧ δ i = 0
    · right
      intro t
      simp [f, hzero.1, hzero.2.1, hzero.2.2]
    · left
      simpa only [f] using
        SphereGeom.Aux.Arrangement.trig_zeros_finite
          (α i) (β i) (δ i) 0 (2 * Real.pi) (by tauto)
  obtain ⟨M, a, b, F0, hF0, hab, hT⟩ :=
    SphereGeom.Aux.Arrangement.finite_nonnegative_intervals k f 0 (2 * Real.pi)
      (by positivity) hf hz
  have hT' : T = (⋃ m, Set.Icc (a m) (b m)) ∪ F0 := hT
  have hbounds (m : Fin M) : 0 ≤ a m ∧ b m ≤ 2 * Real.pi := by
    have ha : a m ∈ T := by
      rw [hT']
      exact Or.inl (Set.mem_iUnion.mpr ⟨m, ⟨le_rfl, (hab m).le⟩⟩)
    have hb : b m ∈ T := by
      rw [hT']
      exact Or.inl (Set.mem_iUnion.mpr ⟨m, ⟨(hab m).le, le_rfl⟩⟩)
    exact ⟨ha.1.1, hb.1.2⟩
  let mid : Fin M → ℝ := fun m => (a m + b m) / 2
  let A : Fin M × Fin 2 → ℝ := fun m => if m.2 = 0 then a m.1 else mid m.1
  let B : Fin M × Fin 2 → ℝ := fun m => if m.2 = 0 then mid m.1 else b m.1
  have hhalf (m : Fin M × Fin 2) : A m < B m ∧ B m - A m < 2 * Real.pi := by
    rcases m with ⟨m, j⟩
    have hm := hab m
    have hbd := hbounds m
    fin_cases j <;> dsimp [A, B, mid] <;>
      constructor <;> nlinarith [Real.pi_pos]
  have hsubset (m : Fin M × Fin 2) :
      Set.Icc (A m) (B m) ⊆ Set.Icc (a m.1) (b m.1) := by
    rcases m with ⟨m, j⟩
    have hm := hab m
    fin_cases j <;> dsimp [A, B, mid]
    · intro t ht
      exact ⟨ht.1, by linarith [ht.2]⟩
    · intro t ht
      exact ⟨by linarith [ht.1], ht.2⟩
  let Γ : (Fin M × Fin 2) → ℝ → E3 := fun m t =>
    circlePt c e1 e2 r (A m + (B m - A m) * t)
  have hΓ (m : Fin M × Fin 2) :
      ContDiff ℝ 2 (Γ m) ∧ Set.InjOn (Γ m) (Set.Icc 0 1) ∧
      (∀ t, deriv (Γ m) t ≠ 0) ∧
      Γ m '' Set.Icc 0 1 = circlePt c e1 e2 r '' Set.Icc (A m) (B m) :=
    SphereGeom.Aux.Arrangement.regular_circle_arc c e1 e2 n hframe r (A m) (B m)
      hr (hhalf m).1 (hhalf m).2
  let E : Fin M × Fin 2 ≃ Fin (M * 2) := finProdFinEquiv
  let γ : Fin (M * 2) → ℝ → E3 := fun j => Γ (E.symm j)
  refine ⟨M * 2, γ, circlePt c e1 e2 r '' F0, hF0.image _,
    (fun j => (hΓ (E.symm j)).1),
    (fun j => (hΓ (E.symm j)).2.1),
    (fun j t _ => (hΓ (E.symm j)).2.2.1 t), ?_⟩
  change circlePt c e1 e2 r '' T = _
  rw [hT', Set.image_union]
  suffices himage : circlePt c e1 e2 r '' (⋃ m, Set.Icc (a m) (b m)) =
      ⋃ j, γ j '' Set.Icc 0 1 by
    rw [himage]
  ext x
  constructor
  · rintro ⟨t, ht, htx⟩
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ht
    by_cases htm : t ≤ mid m
    · apply Set.mem_iUnion.mpr
      refine ⟨E (m, 0), ?_⟩
      change x ∈ Γ (E.symm (E (m, 0))) '' Set.Icc 0 1
      rw [Equiv.symm_apply_apply, (hΓ (m, 0)).2.2.2]
      refine ⟨t, ?_, htx⟩
      simpa [A, B] using (show t ∈ Set.Icc (a m) (mid m) from ⟨hm.1, htm⟩)
    · apply Set.mem_iUnion.mpr
      refine ⟨E (m, 1), ?_⟩
      change x ∈ Γ (E.symm (E (m, 1))) '' Set.Icc 0 1
      rw [Equiv.symm_apply_apply, (hΓ (m, 1)).2.2.2]
      refine ⟨t, ?_, htx⟩
      simpa [A, B] using
        (show t ∈ Set.Icc (mid m) (b m) from ⟨(lt_of_not_ge htm).le, hm.2⟩)
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    change x ∈ Γ (E.symm j) '' Set.Icc 0 1 at hj
    rw [(hΓ (E.symm j)).2.2.2] at hj
    rcases hj with ⟨t, ht, htx⟩
    exact ⟨t, Set.mem_iUnion.mpr ⟨(E.symm j).1, hsubset (E.symm j) ht⟩, htx⟩
