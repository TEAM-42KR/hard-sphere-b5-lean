import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_ConvexCone_positive_smul_transport
set_option autoImplicit false
open SphereGeom Filter
open scoped Topology

theorem proof_SphereGeom_Aux_ConvexCone_line_frontier_unique (C : Set E3) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hscale : ∀ (r : ℝ), 0 ≤ r → ∀ x ∈ C, r • x ∈ C)
    (v n w : E3) (hv : v ∈ interior C) (hnv : 0 < inner ℝ n v)
    (hhalf : ∀ x ∈ C, 0 ≤ inner ℝ n x) :
    ∃ s : ℝ, w + s • v ∈ frontier C ∧
      ∀ t : ℝ, w + t • v ∈ frontier C → t = s := by
  classical
  let A : Set ℝ := {s | w + s • v ∈ C}
  have hline : Continuous (fun s : ℝ => w + s • v) := by fun_prop
  have hAclosed : IsClosed A := hclosed.preimage hline
  have hAne : A.Nonempty := by
    have hcont : ContinuousAt (fun d : ℝ => v + d • w) 0 := by fun_prop
    have hnear : ∀ᶠ d in 𝓝 (0 : ℝ), v + d • w ∈ interior C := by
      apply hcont.eventually
      simpa using isOpen_interior.mem_nhds hv
    have hnear' := hnear.filter_mono
      (show 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have hm : ∀ᶠ d in 𝓝[Set.Ioi (0 : ℝ)] 0, d ∈ Set.Ioi (0 : ℝ) :=
      self_mem_nhdsWithin
    obtain ⟨d, hdv, hd⟩ := (hnear'.and hm).exists
    have hdpos : (0 : ℝ) < d := hd
    refine ⟨d⁻¹, ?_⟩
    have hs := hscale d⁻¹ (inv_pos.mpr hd).le (v + d • w) (interior_subset hdv)
    change w + d⁻¹ • v ∈ C
    convert hs using 1
    simp [smul_add, smul_smul, ne_of_gt hdpos, add_comm]
  have hAbdd : BddBelow A := by
    refine ⟨-(inner ℝ n w) / inner ℝ n v, ?_⟩
    intro s hs
    have hnn := hhalf (w + s • v) hs
    simp only [inner_add_right, inner_smul_right] at hnn
    exact (div_le_iff₀ hnv).mpr (by linarith)
  have hleast : IsLeast A (sInf A) := hAclosed.isLeast_csInf hAne hAbdd
  have hnotinter : w + sInf A • v ∉ interior C := by
    intro hinside
    have hnear : ∀ᶠ t in 𝓝 (sInf A), w + t • v ∈ C :=
      ((hline.continuousAt.eventually (isOpen_interior.mem_nhds hinside)).mono
        fun t ht => interior_subset ht)
    have hnear' := hnear.filter_mono
      (show 𝓝[Set.Iio (sInf A)] (sInf A) ≤ 𝓝 (sInf A) from nhdsWithin_le_nhds)
    have hm : ∀ᶠ t in 𝓝[Set.Iio (sInf A)] (sInf A), t ∈ Set.Iio (sInf A) :=
      self_mem_nhdsWithin
    obtain ⟨t, ht, hts⟩ := (hnear'.and hm).exists
    exact (not_lt_of_ge (hleast.2 ht)) hts
  refine ⟨sInf A, ?_, ?_⟩
  · exact ⟨subset_closure hleast.1, hnotinter⟩
  · intro t ht
    have htc : w + t • v ∈ C := by simpa only [hclosed.closure_eq] using ht.1
    have hst : sInf A ≤ t := hleast.2 htc
    apply le_antisymm _ hst
    by_contra htl
    have hpos : 0 < t - sInf A := sub_pos.mpr (lt_of_not_ge htl)
    have hvscaled : (t - sInf A) • v ∈ interior C :=
      (SphereGeom.Aux.ConvexCone.positive_smul_transport C hscale
        (t - sInf A) hpos v).1.mpr hv
    have hm : (1 / 2 : ℝ) • (w + sInf A • v) +
        (1 / 2 : ℝ) • ((t - sInf A) • v) ∈ interior C :=
      hconvex.combo_self_interior_mem_interior hleast.1 hvscaled
        (by norm_num) (by norm_num) (by norm_num)
    have hs := (SphereGeom.Aux.ConvexCone.positive_smul_transport C hscale
      2 (by norm_num) _).1.mpr hm
    have hi : w + t • v ∈ interior C := by
      convert hs using 1 <;> module
    exact ht.2 hi
