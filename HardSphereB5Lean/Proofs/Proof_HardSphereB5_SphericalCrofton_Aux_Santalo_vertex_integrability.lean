import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

private theorem offAxis_measurable : MeasurableSet {D : Pt | offAxis D} := by
  have heq : ∀ D : Pt, offAxis D ↔ D ≠ (D 0) • e := by
    intro D
    constructor
    · intro h
      exact h (D 0)
    · intro h t ht
      have hcoord := congrArg (fun v : Pt => v 0) ht
      have hdt : D 0 = t := by simpa [e, EuclideanSpace.single_apply] using hcoord
      exact h (hdt ▸ ht)
  simp_rw [heq]
  exact (measurableSet_eq_fun (by fun_prop : Measurable (fun D : Pt => D))
    (by fun_prop : Measurable (fun D : Pt => (D 0) • e))).compl

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_vertex_integrability (f : Kern) :
    IntegrableOn (fun D => if offAxis D ∧ Rc ‖D‖ ‖D - e‖ < 1 then
      2 * Pprim f (min (deltaV D) (Real.pi / 3)) else 0) LamC volume := by
  have hphi : Continuous (phiK f) := by cases f <;> unfold phiK <;> fun_prop
  have hP : Continuous (Pprim f) := by
    exact intervalIntegral.continuous_primitive (fun a b => hphi.intervalIntegrable a b) 0
  have hd : Measurable (fun D : Pt => deltaV D) := by
    unfold deltaV Rc
    fun_prop
  have hRc : Measurable (fun D : Pt => Rc ‖D‖ ‖D - e‖) := by
    unfold Rc
    fun_prop
  have hS : MeasurableSet {D : Pt | offAxis D ∧ Rc ‖D‖ ‖D - e‖ < 1} :=
    offAxis_measurable.inter (measurableSet_lt hRc measurable_const)
  have hm : Measurable (fun D : Pt => if offAxis D ∧ Rc ‖D‖ ‖D - e‖ < 1 then
      2 * Pprim f (min (deltaV D) (Real.pi / 3)) else 0) := by
    exact ((hP.measurable.comp (hd.min measurable_const)).const_mul 2).ite hS measurable_const
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 3))).bddAbove_image
    (hP.norm.continuousOn)
  have hbound : ∀ D : Pt, ‖(if offAxis D ∧ Rc ‖D‖ ‖D - e‖ < 1 then
      2 * Pprim f (min (deltaV D) (Real.pi / 3)) else 0 : ℝ)‖ ≤ 2 * max C 0 := by
    intro D
    split_ifs
    · rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (hC (Set.mem_image_of_mem _ ?_)).trans (le_max_left C 0)
      exact ⟨le_min (Real.arccos_nonneg _) (by positivity), min_le_right _ _⟩
    · simp only [norm_zero]
      positivity
  have hfin : (volume : Measure Pt) LamC < ⊤ := by
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (isCompact_closedBall (0 : Pt) 1).measure_lt_top
  exact IntegrableOn.of_bound hfin hm.aestronglyMeasurable (2 * max C 0)
    (Filter.Eventually.of_forall hbound)
