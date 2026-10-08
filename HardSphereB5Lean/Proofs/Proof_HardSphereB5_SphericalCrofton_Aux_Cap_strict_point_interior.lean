import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Cap_strict_point_interior (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ)
    (w : Metric.sphere (0 : Pt) 1) (hw : ∀ i, h i < inner ℝ (n i) (w : Pt)) :
    (sInterior (⋂ i, cap (n i) (h i))).Nonempty := by
  let U : Set (Metric.sphere (0 : Pt) 1) := ⋂ i, {u | h i < inner ℝ (n i) (u : Pt)}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (by fun_prop)
  have hUsub : U ⊆ (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' (⋂ i, cap (n i) (h i)) := by
    intro u hu
    simp only [Set.mem_preimage, Set.mem_iInter, cap, Set.mem_setOf_eq]
    intro i
    refine ⟨?_, le_of_lt ((Set.mem_iInter.mp hu) i)⟩
    simpa [Metric.mem_sphere, dist_eq_norm] using u.property
  have hwU : w ∈ U := Set.mem_iInter.mpr hw
  have hwi : w ∈ interior ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' (⋂ i, cap (n i) (h i))) :=
    interior_maximal hUsub hU hwU
  exact ⟨w, w, hwi, rfl⟩
