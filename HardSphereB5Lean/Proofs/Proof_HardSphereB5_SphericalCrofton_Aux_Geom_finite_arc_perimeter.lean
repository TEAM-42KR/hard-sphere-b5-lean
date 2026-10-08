import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false
open MeasureTheory SphereGeom
open HardSphereB5.Lean (Pt)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_finite_arc_perimeter (N : ℕ) (γ : Fin N → ℝ → Pt)
    (hγ : ∀ m, ContDiff ℝ 2 (γ m)) :
    arcMeasure (⋃ m, γ m '' Set.Icc (0 : ℝ) 1) < ⊤ := by
  have hm : ∀ m, arcMeasure (γ m '' Set.Icc (0 : ℝ) 1) < ⊤ := by
    intro m
    obtain ⟨K, hK⟩ := (hγ m).contDiffOn.exists_lipschitzOnWith (by norm_num)
      (convex_Icc (0 : ℝ) 1) isCompact_Icc
    have hh := hK.hausdorffMeasure_image_le (d := 1) (by norm_num)
    apply lt_of_le_of_lt hh
    rw [hausdorffMeasure_real]
    simp
  apply lt_of_le_of_lt (measure_iUnion_le _)
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.mpr (fun m _ => hm m)
