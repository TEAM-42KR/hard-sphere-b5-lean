import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_cap_circle_param
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_unit_frame_exists
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_clipped_circle_arcs
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_active_circle_arcs (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m) (h1 : ∀ m, h m < 1) (j : Fin N) :
    ∃ (M : ℕ) (γ : Fin M → ℝ → Pt) (F : Set Pt), F.Finite ∧
      (∀ m, ContDiff ℝ 2 (γ m)) ∧ (∀ m, Set.InjOn (γ m) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (γ m) t ≠ 0) ∧
      ((⋂ m, cap (n m) (h m)) ∩ {u : Pt | inner ℝ (n j) u = h j}) =
        (⋃ m, γ m '' Set.Icc (0 : ℝ) 1) ∪ F := by
  obtain ⟨e1, e2, hframe⟩ := SphereGeom.Aux.Arrangement.unit_frame_exists (n j) (hn j)
  let r := √(1 - (h j) ^ 2)
  let c := (h j) • n j
  let C := circlePt c e1 e2 r
  let α : Fin N → ℝ := fun i => r * inner ℝ (n i) e1
  let β : Fin N → ℝ := fun i => r * inner ℝ (n i) e2
  let δ : Fin N → ℝ := fun i => h i - inner ℝ (n i) c
  have hr : 0 < r := Real.sqrt_pos.mpr (by nlinarith [h0 j, h1 j])
  have hc := SphereGeom.Aux.Arrangement.cap_circle_param e1 e2 (n j) hframe (h j) (h0 j) (h1 j)
  change {u : Pt | ‖u‖ = 1 ∧ inner ℝ (n j) u = h j} = C '' Set.Icc (0 : ℝ) (2 * π) at hc
  have hexp (i : Fin N) (t : ℝ) : inner ℝ (n i) (C t) - h i = α i * cos t + β i * sin t - δ i := by
    dsimp [C, circlePt, α, β, δ]
    simp only [inner_add_right, real_inner_smul_right]
    ring
  have heq : ((⋂ m, cap (n m) (h m)) ∩ {u : Pt | inner ℝ (n j) u = h j}) =
      C '' {t ∈ Set.Icc (0 : ℝ) (2 * π) | ∀ i, 0 ≤ α i * cos t + β i * sin t - δ i} := by
    ext u
    constructor
    · rintro ⟨huK, huj⟩
      have hu1 := (Set.mem_iInter.mp huK j).1
      obtain ⟨t, ht, rfl⟩ := hc ▸ (show u ∈ {u : Pt | ‖u‖ = 1 ∧ inner ℝ (n j) u = h j} from ⟨hu1, huj⟩)
      refine ⟨t, ⟨ht, ?_⟩, rfl⟩
      intro i
      rw [← hexp]
      exact sub_nonneg.mpr (Set.mem_iInter.mp huK i).2
    · rintro ⟨t, ⟨ht, hts⟩, rfl⟩
      have hct : C t ∈ {u : Pt | ‖u‖ = 1 ∧ inner ℝ (n j) u = h j} := by
        rw [hc]
        exact ⟨t, ht, rfl⟩
      refine ⟨Set.mem_iInter.mpr (fun i => ⟨hct.1, ?_⟩), hct.2⟩
      apply sub_nonneg.mp
      rw [hexp]
      exact hts i
  obtain ⟨M, γ, F, hF, hγ, hinj, hderiv, hcover⟩ :=
    SphereGeom.Aux.Arrangement.clipped_circle_arcs N c e1 e2 (n j) hframe r hr α β δ
  exact ⟨M, γ, F, hF, hγ, hinj, hderiv, heq.trans hcover⟩
