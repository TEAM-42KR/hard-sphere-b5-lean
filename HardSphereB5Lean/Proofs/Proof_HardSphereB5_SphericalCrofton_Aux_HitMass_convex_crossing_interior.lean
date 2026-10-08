import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_HitMass_convex_crossing_interior (C : Set Pt) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (hint : (interior C).Nonempty) (p : Pt)
    (hneg : ∃ u ∈ C, inner ℝ p u < 0) (hpos : ∃ u ∈ C, 0 < inner ℝ p u) :
    ∃ v ∈ interior C, inner ℝ p v = 0 := by
  have hclosure : closure (interior C) = C := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hint, hclosed.closure_eq]
  have hc : Continuous (fun u : Pt => inner ℝ p u) := continuous_const.inner continuous_id
  obtain ⟨un, hun, hn⟩ := hneg
  obtain ⟨up, hup, hp⟩ := hpos
  have hunc : un ∈ closure (interior C) := hclosure.symm ▸ hun
  have hupc : up ∈ closure (interior C) := hclosure.symm ▸ hup
  obtain ⟨vn, hvnneg, hvn⟩ := mem_closure_iff.mp hunc {u : Pt | inner ℝ p u < 0}
    (isOpen_lt hc continuous_const) hn
  obtain ⟨vp, hvppos, hvp⟩ := mem_closure_iff.mp hupc {u : Pt | 0 < inner ℝ p u}
    (isOpen_lt continuous_const hc) hp
  have hi := hconv.interior.isPreconnected.intermediate_value hvn hvp hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (inner ℝ p vn) (inner ℝ p vp) from ⟨hvnneg.le, hvppos.le⟩)
  obtain ⟨v, hv, he⟩ := hi
  exact ⟨v, hv, he⟩
