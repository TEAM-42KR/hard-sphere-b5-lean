import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_regular_cone_geometry
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_regular_cone_interior_transport
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_ConvexCone_plane_boundary_pair
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_interior_chord_positive
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_convex_crossing_interior
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_HitMass_support_interior_nonzero
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_HitMass_crossing_boundary_pair {K : Set Pt}
    (hK : IsRegularRegionCrofton K) (p : Pt) (hp : ‖p‖ = 1)
    (hneg : ∃ u ∈ K, inner ℝ p u < 0) (hpos : ∃ u ∈ K, 0 < inner ℝ p u) :
    ∃ a b : Pt, a ≠ b ∧ greatCircle p ∩ sFrontier K = {a, b} ∧
      0 < chordLen K (greatCircle p) := by
  let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}
  obtain ⟨hclosed, hconv, hscale, hint, hfront⟩ := Aux.HitMass.regular_cone_geometry K hK
  change IsClosed C at hclosed
  change Convex ℝ C at hconv
  change ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C at hscale
  change (interior C).Nonempty at hint
  change ∀ u : Pt, ‖u‖ = 1 → (u ∈ frontier C ↔ u ∈ sFrontier K) at hfront
  have hunit (u : Pt) (hu : u ∈ K) : ‖u‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hK.subset_sphere hu
  have hKC : K ⊆ C := by
    intro u hu
    right
    simpa [hunit u hu] using hu
  have hnegC : ∃ u ∈ C, inner ℝ p u < 0 := by
    obtain ⟨u, hu, hh⟩ := hneg
    exact ⟨u, hKC hu, hh⟩
  have hposC : ∃ u ∈ C, 0 < inner ℝ p u := by
    obtain ⟨u, hu, hh⟩ := hpos
    exact ⟨u, hKC hu, hh⟩
  obtain ⟨n, hn, hnK⟩ := hK.in_closed_hemisphere
  have hnC : ∀ v ∈ C, 0 ≤ inner ℝ n v := by
    intro v hv
    rcases hv with rfl | hv
    · simp
    · by_cases hv0 : v = 0
      · simp [hv0]
      · have hvp := norm_pos_iff.mpr hv0
        have h := hnK _ hv
        rw [real_inner_smul_right] at h
        exact nonneg_of_mul_nonneg_right h (inv_pos.mpr hvp)
  obtain ⟨v, hv, hperp⟩ := Aux.HitMass.convex_crossing_interior C hclosed hconv hint p hnegC hposC
  have hv0 : v ≠ 0 := Aux.HitMass.support_interior_nonzero C n hn hnC hv
  have hvp := norm_pos_iff.mpr hv0
  let u := ‖v‖⁻¹ • v
  have hu1 : ‖u‖ = 1 := by
    simpa [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp), ne_of_gt hvp]
  have huint : u ∈ interior C := by
    let H : Pt ≃ₜ Pt := Homeomorph.smulOfNeZero ‖v‖⁻¹ (inv_ne_zero (ne_of_gt hvp))
    have hHC : H ⁻¹' C = C := by
      ext w
      constructor
      · intro hw
        have hh := hscale ‖v‖ hvp.le (H w) hw
        simpa [H, smul_smul, ne_of_gt hvp] using hh
      · intro hw
        exact hscale ‖v‖⁻¹ (inv_pos.mpr hvp).le w hw
    have hHi : H ⁻¹' interior C = interior C := by rw [H.preimage_interior, hHC]
    have hmem : v ∈ H ⁻¹' interior C := hHi.symm ▸ hv
    exact hmem
  have hui : u ∈ sInterior K := (Aux.HitMass.regular_cone_interior_transport K u hu1).mp huint
  have hug : u ∈ greatCircle p := ⟨hu1, by simp [u, real_inner_smul_right, hperp]⟩
  have hlen := Aux.HitMass.interior_chord_positive hK p hp ⟨u, hug, hui⟩
  obtain ⟨a, b, hab, hpairs⟩ := SphereGeom.Aux.ConvexCone.plane_boundary_pair C hclosed hconv
    (show (0 : Pt) ∈ C from Or.inl rfl) hscale p hp ⟨v, hv, hperp⟩ ⟨n, hn, hnC⟩
  refine ⟨a, b, hab, ?_, hlen⟩
  calc greatCircle p ∩ sFrontier K = greatCircle p ∩ frontier C := by
         ext w
         constructor
         · rintro ⟨hwg, hwi⟩
           exact ⟨hwg, (hfront w hwg.1).mpr hwi⟩
         · rintro ⟨hwg, hwi⟩
           exact ⟨hwg, (hfront w hwg.1).mp hwi⟩
       _ = {a, b} := hpairs
