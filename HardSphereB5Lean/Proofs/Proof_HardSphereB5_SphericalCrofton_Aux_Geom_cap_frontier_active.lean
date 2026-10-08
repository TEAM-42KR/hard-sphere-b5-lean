import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_CapIntersection_basic_properties
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_strict_finite_caps_interior
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_active_cap_not_interior
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_cap_heights_lt_one
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_frontier_active (N : ℕ) (hN : 0 < N) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m)
    (hint : (sInterior (⋂ m, cap (n m) (h m))).Nonempty) :
    sFrontier (⋂ m, cap (n m) (h m)) = ⋃ m, ((⋂ i, cap (n i) (h i)) ∩ {u : Pt | inner ℝ (n m) u = h m}) := by
  let K := ⋂ m, cap (n m) (h m)
  have hclosed : IsClosed K := (SphereGeom.Aux.CapIntersection.basic_properties N hN n h hn h0).2.1.isClosed
  have hpreclosed : IsClosed ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' K) := hclosed.preimage continuous_subtype_val
  have hheight := Aux.Geom.cap_heights_lt_one N n h hn hint
  ext u
  constructor
  · rintro ⟨us, hus, rfl⟩
    rw [hpreclosed.frontier_eq] at hus
    have huK : (us : Pt) ∈ K := hus.1
    have hunorm : ‖(us : Pt)‖ = 1 := (Set.mem_iInter.mp huK ⟨0, hN⟩).1
    have hex : ∃ m, inner ℝ (n m) (us : Pt) = h m := by
      by_contra hno
      push_neg at hno
      have hstrict : ∀ m, h m < inner ℝ (n m) (us : Pt) := by
        intro m
        exact lt_of_le_of_ne (Set.mem_iInter.mp huK m).2 (Ne.symm (hno m))
      obtain ⟨v, hv, he⟩ := Aux.Geom.strict_finite_caps_interior N n h (us : Pt) hunorm hstrict
      have hvus : v = us := Subtype.ext he
      exact hus.2 (hvus ▸ hv)
    obtain ⟨m, hm⟩ := hex
    exact Set.mem_iUnion.mpr ⟨m, huK, hm⟩
  · intro hu
    obtain ⟨m, huK, heq⟩ := Set.mem_iUnion.mp hu
    have hunorm : ‖u‖ = 1 := (Set.mem_iInter.mp huK ⟨0, hN⟩).1
    let us : Metric.sphere (0 : Pt) 1 := ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hunorm⟩
    refine ⟨us, ?_, rfl⟩
    rw [hpreclosed.frontier_eq]
    refine ⟨huK, ?_⟩
    intro hi
    have hsub : K ⊆ cap (n m) (h m) := Set.iInter_subset _ m
    have hc : u ∈ sInterior (cap (n m) (h m)) :=
      ⟨us, interior_mono (Set.preimage_mono hsub) hi, rfl⟩
    exact Aux.Geom.active_cap_not_interior (n m) u (h m) (hn m) hunorm (h0 m) (hheight m) heq hc
