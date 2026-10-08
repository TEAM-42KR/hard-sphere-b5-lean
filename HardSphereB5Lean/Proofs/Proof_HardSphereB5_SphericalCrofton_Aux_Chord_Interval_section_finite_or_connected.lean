import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_nonantipodal_joined
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_finite_or_connected {K : Set Pt} (hK : IsRegularRegionCrofton K) (p : Pt) :
    (greatCircle p ∩ K).Finite ∨ IsConnected (greatCircle p ∩ K) := by
  let S : Set Pt := greatCircle p ∩ K
  by_cases hSn : S.Nonempty
  · obtain ⟨u, hu⟩ := hSn
    by_cases hall : S ⊆ ({u, -u} : Set Pt)
    · exact Or.inl (((Set.finite_singleton (-u)).insert u).subset hall)
    · obtain ⟨v, hv, hvpair⟩ := Set.not_subset.mp hall
      have hvu : v ≠ u := by
        intro heq
        exact hvpair (by simp [heq])
      have hvmu : v ≠ -u := by
        intro heq
        exact hvpair (by simp [heq])
      right
      apply IsPathConnected.isConnected
      refine ⟨u, hu, ?_⟩
      intro x hx
      by_cases hux : u ≠ -x
      · exact HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_nonantipodal_joined hK p hu hx hux
      · have hux : u = -x := not_ne_iff.mp hux
        have huv : u ≠ -v := by
          intro hh
          apply hvmu
          simpa [hh] using (show v = v from rfl)
        have hvx : v ≠ -x := by
          intro hh
          exact hvu (hh.trans hux.symm)
        exact (HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_nonantipodal_joined hK p hu hv huv).trans
          (HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_nonantipodal_joined hK p hv hx hvx)
  · exact Or.inl (by change S.Finite; rw [Set.not_nonempty_iff_eq_empty.mp hSn]; exact Set.finite_empty)
