import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false

open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Cap_frontier_slice (n : Pt) (hn : ‖n‖ = 1) (h : ℝ) (h0 : 0 < h) (h1 : h < 1) :
    sFrontier (cap n h) = {u : Pt | ‖u‖ = 1 ∧ inner ℝ n u = h} := by
  let S := Metric.sphere (0 : Pt) 1
  let A : Set S := (Subtype.val : S → Pt) ⁻¹' cap n h
  have hu1 : ∀ u : S, ‖(u : Pt)‖ = 1 := by
    intro u
    simpa [Metric.mem_sphere, dist_zero_right] using u.property
  have hA : A = {u : S | h ≤ inner ℝ n (u : Pt)} := by
    ext u
    change (‖(u : Pt)‖ = 1 ∧ h ≤ inner ℝ n (u : Pt)) ↔ h ≤ inner ℝ n (u : Pt)
    simp [hu1 u]
  have hcA : IsClosed A := by
    rw [hA]
    exact isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  change Subtype.val '' frontier A = _
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hum : u ∈ A := by
      have hh := hu.1
      rwa [hcA.closure_eq] at hh
    have hul : h ≤ inner ℝ n (u : Pt) := by simpa only [hA, Set.mem_setOf_eq] using hum
    refine ⟨hu1 u, le_antisymm ?_ hul⟩
    by_contra hh
    have hs : h < inner ℝ n (u : Pt) := lt_of_not_ge hh
    have hopen : IsOpen {v : S | h < inner ℝ n (v : Pt)} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
    have hsub : {v : S | h < inner ℝ n (v : Pt)} ⊆ A := by
      rw [hA]
      intro v hv
      exact (show h < inner ℝ n (v : Pt) from hv).le
    have hin : u ∈ interior A := interior_mono hsub (by rw [hopen.interior_eq]; exact hs)
    exact hu.2 hin
  · rintro ⟨hx, hnx⟩
    let us : S := ⟨x, by simpa [S, Metric.mem_sphere, dist_zero_right] using hx⟩
    have hmemA : us ∈ A := by rw [hA]; change h ≤ inner ℝ n x; rw [hnx]
    refine ⟨us, ⟨subset_closure hmemA, ?_⟩, rfl⟩
    intro hinter
    have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
    have hxn : inner ℝ x n = h := by rw [real_inner_comm]; exact hnx
    let z : Pt := x - h • n
    have hnz : inner ℝ n z = 0 := by
      change inner ℝ n (x - h • n) = 0
      rw [inner_sub_right, real_inner_smul_right, hnx, hnn]
      ring
    have hzn : inner ℝ z n = 0 := by rw [real_inner_comm]; exact hnz
    have hzz : inner ℝ z z = 1 - h ^ 2 := by
      change inner ℝ (x - h • n) (x - h • n) = 1 - h ^ 2
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        hxx, hnx, hxn, hnn]
      ring
    have hs : 0 < 1 - h ^ 2 := by nlinarith
    let r : ℝ := Real.sqrt (1 - h ^ 2)
    have hr0 : 0 < r := Real.sqrt_pos.2 hs
    have hr2 : r ^ 2 = 1 - h ^ 2 := Real.sq_sqrt hs.le
    let q : Pt := r⁻¹ • z
    have hnq : inner ℝ n q = 0 := by simp [q, real_inner_smul_right, hnz]
    have hqn : inner ℝ q n = 0 := by rw [real_inner_comm]; exact hnq
    have hqq : inner ℝ q q = 1 := by
      change inner ℝ (r⁻¹ • z) (r⁻¹ • z) = 1
      simp only [real_inner_smul_left, real_inner_smul_right, hzz]
      rw [← hr2]
      field_simp
    let D := Set.Ioo (-1 : ℝ) 1
    have hpunit : ∀ t : D, ‖(t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q‖ = 1 := by
      intro t
      have ht0 : 0 ≤ 1 - (t : ℝ) ^ 2 := by nlinarith [t.property.1, t.property.2]
      have htsq := Real.sq_sqrt ht0
      have hh : ‖(t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
          hnn, hnq, hqn, hqq]
        nlinarith
      nlinarith [norm_nonneg ((t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q)]
    let f : D → S := fun t => ⟨(t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q,
      by simpa [S, Metric.mem_sphere, dist_zero_right] using hpunit t⟩
    have hfc : Continuous f := by dsimp [f]; continuity
    let th : D := ⟨h, ⟨by linarith, h1⟩⟩
    have hf0 : f th = us := by
      apply Subtype.ext
      change h • n + r • (r⁻¹ • (x - h • n)) = x
      rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
      abel
    have hpre : f ⁻¹' A = (Subtype.val : D → ℝ) ⁻¹' Set.Ici h := by
      ext t
      change (‖(t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q‖ = 1 ∧
        h ≤ inner ℝ n ((t : ℝ) • n + Real.sqrt (1 - (t : ℝ) ^ 2) • q)) ↔ h ≤ (t : ℝ)
      rw [hpunit t]
      simp only [inner_add_right, real_inner_smul_right, hnn, hnq, mul_one, mul_zero, add_zero, true_and]
    have ht : th ∈ interior (f ⁻¹' A) := preimage_interior_subset_interior_preimage hfc
      (show th ∈ f ⁻¹' interior A by rw [Set.mem_preimage, hf0]; exact hinter)
    rw [hpre] at ht
    have hreal : (th : ℝ) ∈ interior (Set.Ici h) :=
      IsOpenMap.interior_preimage_subset_preimage_interior
        ((isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1)).isOpenEmbedding_subtypeVal.isOpenMap) ht
    have hh : h < h := by simpa [th, interior_Ici] using hreal
    exact lt_irrefl h hh
