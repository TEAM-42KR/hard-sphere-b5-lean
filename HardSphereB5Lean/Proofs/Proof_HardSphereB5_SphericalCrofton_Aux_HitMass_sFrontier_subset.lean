import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_HitMass_sFrontier_subset {K : Set Pt} (hK : IsClosed K) : sFrontier K ⊆ K := by
  rintro x ⟨z, hz, rfl⟩
  have hc : IsClosed ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' K) :=
    hK.preimage continuous_subtype_val
  have hm := frontier_subset_closure hz
  rw [hc.closure_eq] at hm
  exact hm
