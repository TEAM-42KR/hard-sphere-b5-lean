import Mathlib
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_sphere_slice_circle_image
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_pair_arc_subset_circle_pullback
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

private theorem cross_joint_continuous : Continuous (fun z : Pt × Pt => cross z.1 z.2) := by
  unfold cross crossProduct
  fun_prop

private theorem tanA_joint_measurable : Measurable (fun z : Pt × Pt => tanA z.1 z.2) := by
  unfold tanA unitDir nAv cross crossProduct
  fun_prop

private theorem arcA_joint_measurableSet : MeasurableSet {z : Pt × Pt | z.2 ∈ arcA z.1} := by
  have heq : {z : Pt × Pt | z.2 ∈ arcA z.1} =
      {z : Pt × Pt | z.1 ≠ 0 ∧ ‖z.2‖ = 1 ∧ ‖z.1 + z.2‖ ≤ 1 ∧
        dist (z.1 + z.2) e ≤ 1 ∧ ‖z.1 + z.2‖ = 1} := by
    ext z
    by_cases h : z.1 = 0 <;> simp [arcA, SigmaD, LamC, h, and_assoc]
  rw [heq]
  measurability

private theorem phiK_measurable (f : Kern) : Measurable (phiK f) := by
  cases f <;> unfold phiK <;> fun_prop

private theorem cutKern_measurable (f : Kern) : Measurable (cutKern f) := by
  exact (phiK_measurable f).ite (measurableSet_lt measurable_id measurable_const) measurable_const

private theorem AA_joint_kernel_measurable (f : Kern) : Measurable
    (fun z : Pt × (Pt × Pt) =>
      if z.2.1 ∈ arcA z.1 ∧ z.2.2 ∈ arcA z.1 then
        cutKern f (arccos (inner ℝ z.2.1 z.2.2)) *
          santaloDens z.2.1 z.2.2 (tanA z.1 z.2.1) (tanA z.1 z.2.2)
      else 0) := by
  have h1 : Measurable (fun z : Pt × (Pt × Pt) => tanA z.1 z.2.1) := by
    unfold tanA unitDir nAv cross crossProduct
    fun_prop
  have h2 : Measurable (fun z : Pt × (Pt × Pt) => tanA z.1 z.2.2) := by
    unfold tanA unitDir nAv cross crossProduct
    fun_prop
  have hc : Measurable (fun z : Pt × (Pt × Pt) => cross z.2.1 z.2.2) := by
    unfold cross crossProduct
    fun_prop
  have ha : Measurable (fun z : Pt × (Pt × Pt) => arccos (inner ℝ z.2.1 z.2.2)) := by
    exact continuous_arccos.measurable.comp (measurable_snd.fst.inner measurable_snd.snd)
  have hk := (cutKern_measurable f).comp ha
  have hd : Measurable (fun z : Pt × (Pt × Pt) =>
      santaloDens z.2.1 z.2.2 (tanA z.1 z.2.1) (tanA z.1 z.2.2)) := by
    exact (((hc.inner h1).abs.mul (hc.inner h2).abs).div
      ((continuous_sin.measurable.comp ha).pow_const 3))
  exact (hk.mul hd).ite
    ((arcA_joint_measurableSet.preimage (measurable_fst.prodMk measurable_snd.fst)).inter
      (arcA_joint_measurableSet.preimage (measurable_fst.prodMk measurable_snd.snd))) measurable_const

theorem proof_HardSphereB5_SphericalCrofton_Aux_AA_circle_chart_formula (f : Kern) (D : Pt) (hD : D ∈ LamC) (h0 : D ≠ 0) (E : Fin 3 → Pt) (hE : Orthonormal ℝ E) (hn : E 2 = nAv D) : AAf f D = (1 / 2 : ℝ) * (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) ^ 2 * ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π), if circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t ∈ arcA D ∧ circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s ∈ arcA D then cutKern f (arccos (inner ℝ (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t) (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s))) * santaloDens (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t) (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s) (tanA D (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t)) (tanA D (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s)) else 0  := by
  let r : ℝ := Real.sqrt (1 - ‖D‖ ^ 2 / 4)
  let γ : ℝ → Pt := circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) r
  have ha : ‖D‖ ≤ 1 := by
    have hd0 := hD.1
    simpa only [Metric.mem_closedBall, dist_zero_right] using hd0
  have hane : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hr : 0 < r := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg D])
  have hz : |‖D‖ / 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hcenter : (‖D‖ / 2) • E 2 = (-(1 / 2 : ℝ)) • D := by
    rw [hn, nAv, smul_smul, smul_neg]
    rw [neg_smul]
    congr 1
    field_simp
  have hrEq : Real.sqrt (1 - (‖D‖ / 2) ^ 2) = r := by
    dsimp [r]
    congr 1
    ring
  have hsub : arcA D ⊆ γ '' Set.Icc (0 : ℝ) (2 * π) := by
    intro u hu
    simp only [arcA, if_neg h0, Set.mem_setOf_eq, SigmaD] at hu
    have hdinner : inner ℝ D u = -‖D‖ ^ 2 / 2 := by
      have hsum := norm_add_sq_real D u
      rw [hu.2, hu.1.1] at hsum
      nlinarith
    have hninner : inner ℝ (E 2) u = ‖D‖ / 2 := by
      rw [hn, nAv, real_inner_smul_left, inner_neg_left, hdinner]
      field_simp
    have hum : u ∈ {u : Pt | ‖u‖ = 1 ∧ inner ℝ (E 2) u = ‖D‖ / 2} := ⟨hu.1.1, hninner⟩
    rw [SphereGeom.Aux.sphere_slice_circle_image E hE (‖D‖ / 2) hz] at hum
    simpa only [hcenter, hrEq] using hum
  have hE2 : Orthonormal ℝ ![E 0, E 1] := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using orthonormal_iff_ite.mp hE (0 : Fin 3) (0 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (0 : Fin 3) (1 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (1 : Fin 3) (0 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (1 : Fin 3) (1 : Fin 3)
  have hA : MeasurableSet (arcA D) :=
    arcA_joint_measurableSet.preimage (show Measurable (fun u : Pt => (D, u)) from
      measurable_const.prodMk measurable_id)
  let g : Pt × Pt → ℝ := fun uv =>
    if uv.1 ∈ arcA D ∧ uv.2 ∈ arcA D then
      cutKern f (arccos (inner ℝ uv.1 uv.2)) *
        santaloDens uv.1 uv.2 (tanA D uv.1) (tanA D uv.2) else 0
  have hg : Measurable g := (AA_joint_kernel_measurable f).comp
    (show Measurable (fun uv : Pt × Pt => (D, uv)) from measurable_const.prodMk measurable_id)
  have hmasked : AAf f D = (1 / 2 : ℝ) * ∫ u in arcA D, ∫ v in arcA D, g (u,v) ∂arcMeasure ∂arcMeasure := by
    unfold AAf
    congr 1
    apply setIntegral_congr_fun hA
    intro u hu
    apply setIntegral_congr_fun hA
    intro v hv
    simp [g, hu, hv]
  rw [hmasked, SphereGeom.Aux.pair_arc_subset_circle_pullback
    ((-(1 / 2 : ℝ)) • D) ![E 0, E 1] hE2 r hr (arcA D) hA hsub g hg]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← mul_assoc]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  dsimp only [g]
  split_ifs <;> rfl
