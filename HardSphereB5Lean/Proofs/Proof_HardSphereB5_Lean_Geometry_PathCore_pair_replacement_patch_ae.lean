import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_pair_replacement_body
import HardSphereB5Lean.Theorems.Thm_SolidGeom_sphereMeasure_sphere_inter_null
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem proof_HardSphereB5_Lean_Geometry_PathCore_pair_replacement_patch_ae (x : Fin 3 → Pt) (hnd : AffineIndependent ℝ x)
    (ha4 : dist (x 1) (x 2) ^ 2 < 4) (hb : dist (x 0) (x 1) ^ 2 ≤ 1) (hcc : dist (x 0) (x 2) ^ 2 ≤ 1)
    (hlong : dist (x 0) (x 1) ^ 2 ≤ dist (x 1) (x 2) ^ 2 ∧ dist (x 0) (x 2) ^ 2 ≤ dist (x 1) (x 2) ^ 2)
    (hQ : QT (dist (x 1) (x 2) ^ 2) (dist (x 1) (x 0) ^ 2) (dist (x 2) (x 0) ^ 2) ≤ 0) (i : Fin 3) :
    ((⋂ j, Metric.closedBall (x j) 1 : Set Pt)) =ᵐ[SphereGeom.sphereMeasure (x i)]
      ((if i = 0 then ∅ else Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1 : Set Pt)) := by
  have hbody := HardSphereB5.Lean.Geometry.PathCore.pair_replacement_body x hnd ha4 hb hcc hlong hQ
  by_cases hi : i = 0
  · subst i
    simp only [if_pos rfl]
    apply ae_eq_empty.mpr
    have hsub : Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1 ⊆
        Metric.closedBall (x 0) 1 := by
      rw [← hbody]
      exact Set.iInter_subset (fun j => Metric.closedBall (x j) 1) 0
    have hopen : Metric.ball (x 1) 1 ∩ Metric.ball (x 2) 1 ⊆
        interior (Metric.closedBall (x 0) 1) := by
      apply interior_maximal _ (Metric.isOpen_ball.inter Metric.isOpen_ball)
      intro p hp
      exact hsub ⟨Metric.ball_subset_closedBall hp.1, Metric.ball_subset_closedBall hp.2⟩
    have hbound : (⋂ j, Metric.closedBall (x j) 1 : Set Pt) ⊆
        (Metric.sphere (x 1) 1 ∪ Metric.sphere (x 2) 1) ∪ (Metric.sphere (x 0) 1)ᶜ := by
      intro p hp
      by_cases hs : p ∈ Metric.sphere (x 0) 1
      · apply Or.inl
        have hp12 := hbody ▸ hp
        have hp1 : dist p (x 1) ≤ 1 := hp12.1
        have hp2 : dist p (x 2) ≤ 1 := hp12.2
        by_contra hn
        have hn1 : dist p (x 1) ≠ 1 := by
          intro he
          exact hn (Or.inl he)
        have hn2 : dist p (x 2) ≠ 1 := by
          intro he
          exact hn (Or.inr he)
        have hpopen : p ∈ Metric.ball (x 1) 1 ∩ Metric.ball (x 2) 1 :=
          ⟨lt_of_le_of_ne hp1 hn1, lt_of_le_of_ne hp2 hn2⟩
        have hh := hopen hpopen
        rw [interior_closedBall (x 0) (by norm_num : (1 : ℝ) ≠ 0)] at hh
        exact (ne_of_lt hh) hs
      · exact Or.inr hs
    have hn01 : x 0 ≠ x 1 := hnd.injective.ne (by decide)
    have hn02 : x 0 ≠ x 2 := hnd.injective.ne (by decide)
    have hz1 := SolidGeom.sphereMeasure_sphere_inter_null (x 0) (x 1) hn01
    have hz2 := SolidGeom.sphereMeasure_sphere_inter_null (x 0) (x 2) hn02
    have hz0 : SphereGeom.sphereMeasure (x 0) (Metric.sphere (x 0) 1)ᶜ = 0 := by
      rw [SphereGeom.sphereMeasure, Measure.map_apply (by fun_prop) Metric.isClosed_sphere.measurableSet.compl]
      have hempty : (fun u : Metric.sphere (0 : SphereGeom.E3) 1 => x 0 + (u : SphereGeom.E3)) ⁻¹'
          (Metric.sphere (x 0) 1)ᶜ = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro u hu
        apply hu
        simpa [Metric.mem_sphere, dist_eq_norm] using u.property
      rw [hempty, measure_empty]
    exact measure_mono_null hbound (measure_union_null (measure_union_null hz1 hz2) hz0)
  · rw [hbody, if_neg hi]
    exact Filter.EventuallyEq.rfl
