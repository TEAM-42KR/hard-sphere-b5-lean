import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_cap_heights_lt_one
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_cap_frontier_active
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_cap_active_circle_arcs
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_cap_inter_frontier_no_isolated
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_remove_finite_residual
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_boundary_arcs (N : ℕ) (hN : 0 < N) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m)
    (hint : (sInterior (⋂ m, cap (n m) (h m))).Nonempty) :
    ∃ (M : ℕ) (γ : Fin M → ℝ → Pt), (∀ m, ContDiff ℝ 2 (γ m)) ∧
      (∀ m, Set.InjOn (γ m) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (γ m) t ≠ 0) ∧
      sFrontier (⋂ m, cap (n m) (h m)) = ⋃ m, γ m '' Set.Icc (0 : ℝ) 1 := by
  have hh := Aux.Geom.cap_heights_lt_one N n h hn hint
  choose M γ F hF hγ hinj hderiv hcover using
    (fun j => Aux.Geom.cap_active_circle_arcs N n h hn h0 hh j)
  let A : Set Pt := ⋃ j, ⋃ m, γ j m '' Set.Icc (0 : ℝ) 1
  let FT : Set Pt := ⋃ j, F j
  let B : Set Pt := sFrontier (⋂ m, cap (n m) (h m))
  have hA : IsClosed A := by
    apply isClosed_iUnion_of_finite
    intro j
    apply isClosed_iUnion_of_finite
    intro m
    exact (isCompact_Icc.image (hγ j m).continuous).isClosed
  have hFT : FT.Finite := Set.finite_iUnion hF
  have hBAF : B = A ∪ FT := by
    dsimp only [B, A, FT]
    rw [Aux.Geom.cap_frontier_active N hN n h hn h0 hint]
    simp_rw [hcover]
    exact Set.iUnion_union_distrib _ _
  have hBA : B = A := SphereGeom.Aux.Arrangement.remove_finite_residual Pt A FT B hA hFT hBAF
    (Aux.Geom.cap_inter_frontier_no_isolated N hN n h hn h0 hint)
  let T := Σ j : Fin N, Fin (M j)
  let E : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let G : Fin (Fintype.card T) → ℝ → Pt := fun k => γ (E.symm k).1 (E.symm k).2
  refine ⟨Fintype.card T, G, ?_, ?_, ?_, ?_⟩
  · intro k
    exact hγ (E.symm k).1 (E.symm k).2
  · intro k
    exact hinj (E.symm k).1 (E.symm k).2
  · intro k t ht
    exact hderiv (E.symm k).1 (E.symm k).2 t ht
  · change B = ⋃ k, G k '' Set.Icc (0 : ℝ) 1
    rw [hBA]
    ext u
    constructor
    · intro hu
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hu
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hj
      apply Set.mem_iUnion.mpr
      refine ⟨E ⟨j, m⟩, ?_⟩
      dsimp only [G]
      rw [E.symm_apply_apply]
      exact hm
    · intro hu
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hu
      exact Set.mem_iUnion.mpr ⟨(E.symm k).1, Set.mem_iUnion.mpr ⟨(E.symm k).2, hk⟩⟩
