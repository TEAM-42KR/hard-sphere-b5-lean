import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_HitMass_boundary_disjoint_arcs_sigmaCompact {K : Set Pt} (hK : IsRegularRegionCrofton K) :
    ∃ (N : ℕ) (γ : Fin N → ℝ → Pt) (S : Fin N → Set ℝ),
      (∀ m, ContDiff ℝ 1 (γ m)) ∧
      (∀ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖γ m t‖ = 1) ∧
      (∀ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (γ m) t ≠ 0) ∧
      (∀ m, Set.InjOn (γ m) (Set.Icc 0 1)) ∧
      (∀ m, MeasurableSet (S m)) ∧
      (∀ m, S m ⊆ Set.Icc 0 1) ∧
      (∀ m, MeasurableSet (γ m '' S m)) ∧
      (Pairwise fun i j => Disjoint (γ i '' S i) (γ j '' S j)) ∧
      (∀ m, IsSigmaCompact (γ m '' S m)) ∧
      sFrontier K = ⋃ m, γ m '' S m := by
  classical
  obtain ⟨N, γ, hγ, hinj, hreg, hcover⟩ := hK.boundary_C2_arcs
  let A : Fin N → Set Pt := fun m => γ m '' Set.Icc 0 1
  let D : Fin N → Set Pt := disjointed A
  let S : Fin N → Set ℝ := fun m => Set.Icc 0 1 ∩ γ m ⁻¹' D m
  have hAcl : ∀ m, IsClosed (A m) := fun m => (isCompact_Icc.image (hγ m).continuous).isClosed
  have hDlc : ∀ m, IsLocallyClosed (D m) := by
    intro m
    dsimp [D]
    rw [disjointed_eq_inter_compl]
    apply (hAcl m).isLocallyClosed.inter
    apply IsOpen.isLocallyClosed
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro hj
    exact (hAcl j).isOpen_compl
  have hDsigma : ∀ m, IsSigmaCompact (D m) := by
    intro m
    letI : LocallyCompactSpace (D m) := (hDlc m).locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have hA : ∀ m, MeasurableSet (A m) := by
    intro m
    exact (isCompact_Icc.image (hγ m).continuous).measurableSet
  have hD : ∀ m, MeasurableSet (D m) := by
    intro m
    dsimp [D]
    rw [disjointed_eq_inter_compl]
    exact (hA m).inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hA j).compl)
  have hsub : ∀ m, D m ⊆ A m := fun m => disjointed_subset A m
  have heq : ∀ m, γ m '' S m = D m := by
    intro m
    apply Set.Subset.antisymm
    · rintro y ⟨t, ht, rfl⟩
      exact ht.2
    · intro y hy
      obtain ⟨t, ht, hty⟩ := hsub m hy
      refine ⟨t, ⟨ht, ?_⟩, hty⟩
      change γ m t ∈ D m
      rwa [hty]
  have hsf : sFrontier K ⊆ Metric.sphere (0 : Pt) 1 := by
    rintro x ⟨z, hz, rfl⟩
    exact z.property
  refine ⟨N, γ, S, (fun m => (hγ m).of_le (by norm_num)), ?_, hreg, hinj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m t ht
    have hm : γ m t ∈ sFrontier K := by
      rw [hcover]
      exact Set.mem_iUnion.mpr ⟨m, ⟨t, ht, rfl⟩⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using hsf hm
  · intro m
    exact measurableSet_Icc.inter ((hD m).preimage (hγ m).continuous.measurable)
  · intro m t ht
    exact ht.1
  · intro m
    rw [heq m]
    exact hD m
  · intro i j hij
    rw [heq i, heq j]
    exact disjoint_disjointed A hij
  · intro m
    rw [heq m]
    exact hDsigma m
  · simp_rw [heq]
    exact hcover.trans iUnion_disjointed.symm
