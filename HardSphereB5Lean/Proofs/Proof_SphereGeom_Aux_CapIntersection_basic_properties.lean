import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom MeasureTheory

noncomputable section

theorem proof_SphereGeom_Aux_CapIntersection_basic_properties (N : ℕ) (hN : 0 < N) (n : Fin N → E3) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m) :
    (⋂ m, cap (n m) (h m)) ⊆ Metric.sphere (0 : E3) 1 ∧
    IsCompact (⋂ m, cap (n m) (h m)) ∧
    (∃ z : E3, z ≠ 0 ∧ ∀ u ∈ ⋂ m, cap (n m) (h m), 0 ≤ inner ℝ z u) ∧
    (∀ u ∈ ⋂ m, cap (n m) (h m), ∀ v ∈ ⋂ m, cap (n m) (h m), u ≠ -v →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - t) • u + t • v‖⁻¹ • ((1 - t) • u + t • v) ∈ ⋂ m, cap (n m) (h m)) := by
  let m0 : Fin N := ⟨0, hN⟩
  have hsub : (⋂ m, cap (n m) (h m)) ⊆ Metric.sphere (0 : E3) 1 := by
    intro u hu
    have hu0 := (Set.mem_iInter.mp hu m0).1
    simpa [Metric.mem_sphere, dist_zero_right] using hu0
  have hclosed : IsClosed (⋂ m, cap (n m) (h m)) := by
    apply isClosed_iInter
    intro m
    have hc : Continuous (fun u : E3 => inner ℝ (n m) u) := continuous_const.inner continuous_id
    exact (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_le continuous_const hc)
  refine ⟨hsub, (isCompact_sphere (0 : E3) 1).of_isClosed_subset hclosed hsub, ?_, ?_⟩
  · refine ⟨n m0, ?_, ?_⟩
    · intro hn0
      have hnorm := hn m0
      simp [hn0] at hnorm
    · intro u hu
      exact (h0 m0).trans (Set.mem_iInter.mp hu m0).2
  · intro u hu v hv huv t ht
    have hu1 : ‖u‖ = 1 := (Set.mem_iInter.mp hu m0).1
    have hv1 : ‖v‖ = 1 := (Set.mem_iInter.mp hv m0).1
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    let x : E3 := (1 - t) • u + t • v
    have hx0 : x ≠ 0 := by
      intro hx
      have hvec : (1 - t) • u = -(t • v) := eq_neg_of_add_eq_zero_left hx
      have hcoeff : 1 - t = t := by
        have hh := congrArg norm hvec
        simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg ht1, hu1, hv1] using hh
      have htne : t ≠ 0 := by linarith
      have hsum : t • (u + v) = 0 := by
        calc
          t • (u + v) = (1 - t) • u + t • v := by rw [smul_add, hcoeff]
          _ = 0 := hx
      have huv0 : u + v = 0 := (smul_eq_zero.mp hsum).resolve_left htne
      exact huv (eq_neg_of_add_eq_zero_left huv0)
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hx1 : ‖x‖ ≤ 1 := by
      have hb := norm_add_le ((1 - t) • u) (t • v)
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg ht1, hu1, hv1] using hb
    have hinv : 1 ≤ ‖x‖⁻¹ := (one_le_inv₀ hxpos).mpr hx1
    have hxnorm : ‖‖x‖⁻¹ • x‖ = 1 := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos), ne_of_gt hxpos]
    apply Set.mem_iInter.mpr
    intro m
    refine ⟨hxnorm, ?_⟩
    have hmu := (Set.mem_iInter.mp hu m).2
    have hmv := (Set.mem_iInter.mp hv m).2
    have hlin : h m ≤ inner ℝ (n m) x := by
      dsimp [x]
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      nlinarith [mul_nonneg ht1 (sub_nonneg.mpr hmu), mul_nonneg ht0 (sub_nonneg.mpr hmv)]
    have hnon : 0 ≤ inner ℝ (n m) x := (h0 m).trans hlin
    rw [inner_smul_right]
    nlinarith [mul_nonneg (sub_nonneg.mpr hinv) hnon]
