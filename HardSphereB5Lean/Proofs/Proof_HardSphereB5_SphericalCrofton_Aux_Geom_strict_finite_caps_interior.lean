import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_strict_finite_caps_interior (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ) (u : Pt)
    (hu : ‖u‖ = 1) (hs : ∀ m, h m < inner ℝ (n m) u) :
    u ∈ sInterior (⋂ m, cap (n m) (h m)) := by
  let us : Metric.sphere (0 : Pt) 1 := ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu⟩
  let O := ⋂ m, {v : Metric.sphere (0 : Pt) 1 | h m < inner ℝ (n m) (v : Pt)}
  have hopen : IsOpen O := by
    apply isOpen_iInter_of_finite
    intro m
    have hc : Continuous (fun v : Metric.sphere (0 : Pt) 1 => inner ℝ (n m) (v : Pt)) := continuous_const.inner continuous_subtype_val
    exact isOpen_lt continuous_const hc
  have hsub : O ⊆ (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' (⋂ m, cap (n m) (h m)) := by
    intro v hv
    apply Set.mem_iInter.mpr
    intro m
    refine ⟨?_, (Set.mem_iInter.mp hv m).le⟩
    simpa [Metric.mem_sphere, dist_zero_right] using v.property
  refine ⟨us, interior_mono hsub ?_, rfl⟩
  rw [hopen.interior_eq]
  exact Set.mem_iInter.mpr hs
