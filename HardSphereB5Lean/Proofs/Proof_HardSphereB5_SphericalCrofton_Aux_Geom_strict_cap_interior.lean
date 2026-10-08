import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_strict_cap_interior (x y u : Pt) (a b : ℝ)
    (hu : ‖u‖ = 1) (hx : a < inner ℝ x u) (hy : b < inner ℝ y u) :
    u ∈ sInterior {v : Pt | ‖v‖ = 1 ∧ a ≤ inner ℝ x v ∧ b ≤ inner ℝ y v} := by
  let us : Metric.sphere (0 : Pt) 1 := ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu⟩
  have hc1 : Continuous (fun v : Metric.sphere (0 : Pt) 1 => inner ℝ x (v : Pt)) := continuous_const.inner continuous_subtype_val
  have hc2 : Continuous (fun v : Metric.sphere (0 : Pt) 1 => inner ℝ y (v : Pt)) := continuous_const.inner continuous_subtype_val
  have hopen : IsOpen {v : Metric.sphere (0 : Pt) 1 | a < inner ℝ x (v : Pt) ∧ b < inner ℝ y (v : Pt)} :=
    (isOpen_lt continuous_const hc1).inter (isOpen_lt continuous_const hc2)
  have hsub : {v : Metric.sphere (0 : Pt) 1 | a < inner ℝ x (v : Pt) ∧ b < inner ℝ y (v : Pt)} ⊆
      (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' {v : Pt | ‖v‖ = 1 ∧ a ≤ inner ℝ x v ∧ b ≤ inner ℝ y v} := by
    intro v hv
    refine ⟨?_, hv.1.le, hv.2.le⟩
    simpa [Metric.mem_sphere, dist_zero_right] using v.property
  refine ⟨us, interior_mono hsub ?_, rfl⟩
  rw [hopen.interior_eq]
  exact ⟨hx, hy⟩
