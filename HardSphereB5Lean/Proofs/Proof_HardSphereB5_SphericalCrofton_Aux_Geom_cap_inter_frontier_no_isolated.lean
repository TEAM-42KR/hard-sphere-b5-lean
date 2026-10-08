import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_cap_inter_density
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_CapIntersection_basic_properties
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 1000000

open Set Metric Topology

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_inter_frontier_no_isolated (N : ℕ) (hN : 0 < N) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m)
    (hint : (sInterior (⋂ m, cap (n m) (h m))).Nonempty) :
    ∀ u ∈ sFrontier (⋂ m, cap (n m) (h m)), ∀ ε > 0,
      ∃ v ∈ sFrontier (⋂ m, cap (n m) (h m)), v ≠ u ∧ dist v u < ε := by
  let V := EuclideanSpace ℝ (Fin 2)
  have hdim : 1 < Module.rank ℝ V := by
    rw [← Module.finrank_eq_rank]
    norm_num [V, finrank_euclideanSpace]
  have hpunc : ∀ (x : V) (r : ℝ), 0 < r →
      IsPreconnected (Metric.ball x r \ {x}) := by
    intro x r hr
    let b : OpenPartialHomeomorph V V := OpenPartialHomeomorph.univBall x r
    have hb0 : b 0 = x := by simp [b]
    have hbs : b.source = Set.univ := by simp [b]
    have hbt : b.target = Metric.ball x r := by
      exact OpenPartialHomeomorph.univBall_target x hr
    have hbi : Function.Injective b := (b.isOpenEmbedding hbs).injective
    have hbc : Continuous b := by simpa [b] using OpenPartialHomeomorph.continuous_univBall x r
    have him : b '' ({0}ᶜ : Set V) = Metric.ball x r \ {x} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [← hbt]; exact b.map_source (by rw [hbs]; trivial)
        · simp only [Set.mem_singleton_iff]
          intro he; exact hz (Set.mem_singleton_iff.mpr (hbi (he.trans hb0.symm)))
      · intro hy
        have hyt : y ∈ b.target := by rw [hbt]; exact hy.1
        refine ⟨b.symm y, ?_, b.right_inv hyt⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro he
        have hh : y = x := by rw [← b.right_inv hyt, he, hb0]
        exact hy.2 (Set.mem_singleton_iff.mpr hh)
    rw [← him]
    exact (isConnected_compl_singleton_of_one_lt_rank hdim (0 : V)).isPreconnected.image b hbc.continuousOn
  have heuc : ∀ (A : Set V), IsClosed A → A ⊆ closure (interior A) →
      ∀ x ∈ frontier A, ∀ r > 0, ∃ y ∈ frontier A, y ≠ x ∧ dist y x < r := by
    intro A hclosed hreg x hx r hr
    by_contra hno
    have havoid : ∀ y ∈ Metric.ball x r \ {x}, y ∉ frontier A := by
      intro y hy hfront
      exact hno ⟨y, hfront, by simpa using hy.2, hy.1⟩
    have hxA : x ∈ A := by rw [← hclosed.closure_eq]; exact frontier_subset_closure hx
    have hxni : x ∉ interior A := hx.2
    have hxc : x ∈ closure (interior A) := hreg hxA
    obtain ⟨p, hpI, hpd⟩ := Metric.mem_closure_iff.mp hxc r hr
    have hpne : p ≠ x := by intro he; exact hxni (he ▸ hpI)
    have hp : p ∈ Metric.ball x r \ {x} := ⟨by simpa [dist_comm] using hpd, by simpa using hpne⟩
    have hxc' : x ∈ closure Aᶜ := by rw [frontier_eq_closure_inter_closure] at hx; exact hx.2
    obtain ⟨q, hqC, hqd⟩ := (Metric.mem_closure_iff (s := (Aᶜ : Set V)) (a := x)).mp hxc' r hr
    have hqne : q ≠ x := by intro he; exact hqC (he ▸ hxA)
    have hq : q ∈ Metric.ball x r \ {x} := ⟨by simpa [dist_comm] using hqd, by simpa using hqne⟩
    have hcover : Metric.ball x r \ {x} ⊆ interior A ∪ Aᶜ := by
      intro y hy
      by_cases hyA : y ∈ A
      · left
        by_contra hyi
        exact havoid y hy ⟨subset_closure hyA, hyi⟩
      · exact Or.inr hyA
    have hdisj : Disjoint (interior A) Aᶜ := Set.disjoint_left.mpr (fun y hy hyc => hyc (interior_subset hy))
    have hsub := (hpunc x r hr).subset_left_of_subset_union isOpen_interior hclosed.isOpen_compl hdisj hcover ⟨p, hp, hpI⟩
    exact hqC (interior_subset (hsub hq))
  let K := ⋂ m, cap (n m) (h m)
  let S := Metric.sphere (0 : Pt) 1
  let A : Set S := (Subtype.val : S → Pt) ⁻¹' K
  have hclosedK : IsClosed K := (SphereGeom.Aux.CapIntersection.basic_properties N hN n h hn h0).2.1.isClosed
  have hclosedA : IsClosed A := hclosedK.preimage continuous_subtype_val
  have hden : K = closure (sInterior K) := HardSphereB5.SphericalCrofton.Aux.Geom.cap_inter_density N hN n h hn h0 hint
  have hregA : A ⊆ closure (interior A) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    intro z hz
    change (z : Pt) ∈ closure (sInterior K)
    rw [← hden]
    exact hz
  rintro u ⟨us, hus, rfl⟩ ε hε
  letI : Fact (Module.finrank ℝ Pt = 2 + 1) := ⟨by simp [HardSphereB5.Lean.Pt]⟩
  let c : OpenPartialHomeomorph S V := stereographic' 2 (-us)
  have hct : c.target = Set.univ := by simp [c, stereographic'_target]
  have hcs : us ∈ c.source := by
    simp [c, stereographic'_source, ne_neg_of_mem_unit_sphere ℝ us]
  let f : V → S := c.symm
  have hf : Continuous f := by
    simpa only [f, hct, continuousOn_univ] using c.continuousOn_symm
  have hfo : IsOpenMap f := (c.symm.isOpenEmbedding (by simpa using hct)).isOpenMap
  have hfi : Function.Injective f := (c.symm.isOpenEmbedding (by simpa using hct)).injective
  let B : Set V := f ⁻¹' A
  have hclosedB : IsClosed B := hclosedA.preimage hf
  have hregB : B ⊆ closure (interior B) := by
    intro z hz
    have hh : f z ∈ closure (interior A) := hregA hz
    have hh' : z ∈ closure (f ⁻¹' interior A) := hfo.preimage_closure_subset_closure_preimage hh
    rw [hfo.preimage_interior_eq_interior_preimage hf A] at hh'
    exact hh'
  let x : V := c us
  have hfx : f x = us := c.left_inv hcs
  have hxF : x ∈ frontier B := by
    rw [← hfo.preimage_frontier_eq_frontier_preimage hf A]
    change f x ∈ frontier A
    rw [hfx]
    exact hus
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
  obtain ⟨y, hyF, hyne, hyd⟩ := heuc B hclosedB hregB x hxF δ hδ
  have hyA : f y ∈ frontier A := by
    rw [← hfo.preimage_frontier_eq_frontier_preimage hf A] at hyF
    exact hyF
  refine ⟨(f y : Pt), ⟨f y, hyA, rfl⟩, ?_, ?_⟩
  · intro he
    have he' : f y = us := Subtype.ext he
    have : y = x := hfi (he'.trans hfx.symm)
    exact hyne this
  · have hh := hδf hyd
    simpa [hfx, Subtype.dist_eq] using hh
