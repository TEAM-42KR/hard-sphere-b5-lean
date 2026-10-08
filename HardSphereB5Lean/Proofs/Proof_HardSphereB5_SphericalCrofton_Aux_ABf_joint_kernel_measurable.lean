import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 600000

theorem proof_HardSphereB5_SphericalCrofton_Aux_ABf_joint_kernel_measurable (f : Kern) : Measurable
    (fun z : Pt × (Pt × Pt) =>
      if z.2.1 ∈ arcA z.1 ∧ z.2.2 ∈ arcB z.1 then
        cutKern f (arccos (inner ℝ z.2.1 z.2.2)) *
          santaloDens z.2.1 z.2.2 (tanA z.1 z.2.1) (tanB z.1 z.2.2) else 0) := by
  have hA : MeasurableSet {z : Pt × Pt | z.2 ∈ arcA z.1} := by
    have heq : {z : Pt × Pt | z.2 ∈ arcA z.1} =
        {z : Pt × Pt | z.1 ≠ 0 ∧ ‖z.2‖ = 1 ∧ ‖z.1 + z.2‖ ≤ 1 ∧
          dist (z.1 + z.2) e ≤ 1 ∧ ‖z.1 + z.2‖ = 1} := by
      ext z
      by_cases h : z.1 = 0 <;> simp [arcA, SigmaD, LamC, h, and_assoc]
    rw [heq]
    measurability
  have hB : MeasurableSet {z : Pt × Pt | z.2 ∈ arcB z.1} := by
    have heq : {z : Pt × Pt | z.2 ∈ arcB z.1} =
        {z : Pt × Pt | z.1 ≠ e ∧ ‖z.2‖ = 1 ∧ ‖z.1 + z.2‖ ≤ 1 ∧
          dist (z.1 + z.2) e ≤ 1 ∧ dist (z.1 + z.2) e = 1} := by
      ext z
      by_cases h : z.1 = e <;> simp [arcB, SigmaD, LamC, h, and_assoc]
    rw [heq]
    measurability
  have hTA : Measurable (fun z : Pt × (Pt × Pt) => tanA z.1 z.2.1) := by
    unfold tanA unitDir nAv cross crossProduct
    fun_prop
  have hTB : Measurable (fun z : Pt × (Pt × Pt) => tanB z.1 z.2.2) := by
    unfold tanB unitDir nBv cross crossProduct
    fun_prop
  have hcross : Measurable (fun z : Pt × (Pt × Pt) => cross z.2.1 z.2.2) := by
    unfold cross crossProduct
    fun_prop
  have hx : Measurable (fun z : Pt × (Pt × Pt) => inner ℝ z.2.1 z.2.2) :=
    measurable_snd.fst.inner measurable_snd.snd
  have hangle : Measurable (fun z : Pt × (Pt × Pt) => arccos (inner ℝ z.2.1 z.2.2)) :=
    Real.continuous_arccos.measurable.comp hx
  have hPhi : Measurable (phiK f) := by
    cases f <;> unfold phiK <;> fun_prop
  have hcut : Measurable (fun z : Pt × (Pt × Pt) =>
      cutKern f (arccos (inner ℝ z.2.1 z.2.2))) := by
    unfold cutKern
    exact (hPhi.comp hangle).ite
      (measurableSet_lt hangle measurable_const) measurable_const
  have hdens : Measurable (fun z : Pt × (Pt × Pt) =>
      santaloDens z.2.1 z.2.2 (tanA z.1 z.2.1) (tanB z.1 z.2.2)) := by
    unfold santaloDens
    exact (((hcross.inner hTA).abs).mul ((hcross.inner hTB).abs)).div
      ((Real.continuous_sin.measurable.comp hangle).pow_const 3)
  exact (hcut.mul hdens).ite
    ((hA.preimage (measurable_fst.prodMk measurable_snd.fst)).inter
      (hB.preimage (measurable_fst.prodMk measurable_snd.snd))) measurable_const
