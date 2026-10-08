import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_center_frame_orthonormal
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_circle_image
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_restrict_circle
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_pullback (p p' : Pt)
    (hd : p'-p ≠ 0) (hf : centerFrame0 (p'-p) ≠ 0)
    (g : Pt → ℝ) (hg : Measurable g) :
    (∫ q in {q : Pt | ‖q‖ = 1 ∧ inner ℝ q (p'-p) = 0 ∧
        midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) • q ∈ LamC},
      g (midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) • q) ∂arcMeasure) =
    ∫ ψ in Set.Icc (-Real.pi) Real.pi,
      if midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) •
        (Real.cos ψ • centerFrame0 (p'-p) + Real.sin ψ • centerFrame1 (p'-p)) ∈ LamC
      then g (midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) •
        (Real.cos ψ • centerFrame0 (p'-p) + Real.sin ψ • centerFrame1 (p'-p))) else 0  := by
  let d : Pt := p'-p
  let F0 : Pt := centerFrame0 d
  let F1 : Pt := centerFrame1 d
  let I : Set ℝ := Set.Icc (-Real.pi) Real.pi
  let γ : ℝ → Pt := circlePt 0 F0 F1 1
  let r : ℝ := Real.sqrt (1-dist p p'^2/4)
  let H : Pt → Pt := fun q => midpoint ℝ p p' + r • q
  let A : Set Pt := {q | ‖q‖ = 1 ∧ inner ℝ q d = 0 ∧ H q ∈ LamC}
  have hframe := HardSphereB5.SphericalCrofton.Aux.Coarea.center_frame_orthonormal d hd hf
  have hE : Orthonormal ℝ ![F0,F1] := by
    rw [orthonormal_iff_ite]
    have h := orthonormal_iff_ite.mp hframe
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [F0, F1] using h 0 0
    · simpa [F0, F1] using h 0 1
    · simpa [F0, F1] using h 1 0
    · simpa [F0, F1] using h 1 1
  have hinner (q : Pt) : inner ℝ (unitDir d) q = 0 ↔ inner ℝ q d = 0 := by
    rw [unitDir, real_inner_smul_left, real_inner_comm]
    have hn : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    simp [mul_eq_zero, hn]
  have himage : γ '' I = greatCircle (unitDir d) :=
    SphereGeom.Aux.Pair.circle_image F0 F1 (unitDir d) hframe
  have hsub : A ⊆ γ '' I := by
    intro q hq
    rw [himage]
    exact ⟨hq.1, (hinner q).mpr hq.2.1⟩
  have hH : Continuous H := by dsimp [H]; fun_prop
  have hL : MeasurableSet LamC := (Metric.isClosed_closedBall.inter Metric.isClosed_closedBall).measurableSet
  have hA : MeasurableSet A := by
    have hn : MeasurableSet {q : Pt | ‖q‖ = 1} :=
      (isClosed_eq continuous_norm continuous_const).measurableSet
    have hi : MeasurableSet {q : Pt | inner ℝ q d = 0} :=
      (isClosed_eq (by fun_prop : Continuous (fun q : Pt => inner ℝ q d)) continuous_const).measurableSet
    exact hn.inter (hi.inter (hL.preimage hH.measurable))
  have hγ : Measurable γ := by dsimp [γ]; unfold circlePt; fun_prop
  have hm : arcMeasure.restrict (γ '' I) = (volume.restrict I).map γ := by
    have h := SphereGeom.arcMeasure_restrict_circle 0 ![F0,F1] hE 1 (by norm_num)
      (-Real.pi) Real.pi (by linarith [Real.pi_pos]) (by linarith)
    simpa [γ, I] using h
  have hk : Measurable (fun q => g (H q)) := hg.comp hH.measurable
  change (∫ q in A, g (H q) ∂arcMeasure) = _
  calc
    (∫ q in A, g (H q) ∂arcMeasure) =
      ∫ q in A, g (H q) ∂(arcMeasure.restrict (γ '' I)) := by
        rw [Measure.restrict_restrict_of_subset hsub]
    _ = ∫ q, A.indicator (fun q => g (H q)) q ∂(arcMeasure.restrict (γ '' I)) :=
      (integral_indicator hA).symm
    _ = ∫ ψ in I, A.indicator (fun q => g (H q)) (γ ψ) := by
      rw [hm, integral_map_of_stronglyMeasurable hγ (hk.stronglyMeasurable.indicator hA)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with ψ hψ
      have hq : γ ψ ∈ greatCircle (unitDir d) := by
        rw [← himage]; exact ⟨ψ,hψ,rfl⟩
      have hmψ : γ ψ ∈ A ↔ H (γ ψ) ∈ LamC := by
        simp only [A, Set.mem_setOf_eq, hq.1, (hinner (γ ψ)).mp hq.2, true_and]
      simp only [Set.indicator_apply, hmψ]
      simp [H, γ, circlePt, r, F0, F1, d]

