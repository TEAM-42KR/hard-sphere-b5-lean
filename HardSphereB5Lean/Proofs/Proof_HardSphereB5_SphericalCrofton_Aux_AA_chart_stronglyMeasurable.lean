import Mathlib
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

theorem proof_HardSphereB5_SphericalCrofton_Aux_AA_chart_stronglyMeasurable (f : Kern) (p : Pt × ℝ → Pt) (hp : Measurable p)
    (r : Pt → ℝ) (hr : Measurable r) : StronglyMeasurable
    (fun D : Pt => (1 / 2 : ℝ) * (r D) ^ 2 *
      ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π),
        if p (D, t) ∈ arcA D ∧ p (D, s) ∈ arcA D then
          cutKern f (arccos (inner ℝ (p (D, t)) (p (D, s)))) *
            santaloDens (p (D, t)) (p (D, s)) (tanA D (p (D, t))) (tanA D (p (D, s)))
        else 0) := by
  let H : (Pt × ℝ) × ℝ → ℝ := fun z =>
    if p (z.1.1, z.1.2) ∈ arcA z.1.1 ∧ p (z.1.1, z.2) ∈ arcA z.1.1 then
      cutKern f (arccos (inner ℝ (p (z.1.1, z.1.2)) (p (z.1.1, z.2)))) *
        santaloDens (p (z.1.1, z.1.2)) (p (z.1.1, z.2))
          (tanA z.1.1 (p (z.1.1, z.1.2))) (tanA z.1.1 (p (z.1.1, z.2))) else 0
  have hmap : Measurable (fun z : (Pt × ℝ) × ℝ =>
      (z.1.1, (p (z.1.1, z.1.2), p (z.1.1, z.2)))) := by
    exact measurable_fst.fst.prodMk
      ((hp.comp measurable_fst).prodMk (hp.comp (measurable_fst.fst.prodMk measurable_snd)))
  have hH : Measurable H := (AA_joint_kernel_measurable f).comp hmap
  have hinner : StronglyMeasurable (fun z : Pt × ℝ =>
      ∫ s in Set.Icc (0 : ℝ) (2 * π), H (z, s)) := hH.stronglyMeasurable.integral_prod_right'
  have houter : StronglyMeasurable (fun D : Pt =>
      ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π), H ((D, t), s)) :=
    hinner.integral_prod_right'
  exact ((stronglyMeasurable_const.mul (hr.pow_const 2).stronglyMeasurable).mul houter)
