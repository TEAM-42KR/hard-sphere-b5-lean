import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 600000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Bf_joint_kernel_measurable (f : Kern) : Measurable
    (fun z : Pt × (Pt × Pt) =>
      if z.2.1 ∈ arcA z.1 ∧ z.2.2 ∈ arcB z.1 then
        (if 1 / 2 < inner ℝ z.2.1 z.2.2 then
          rhoK f (inner ℝ z.2.1 z.2.2) * inner ℝ (nAv z.1) (cross z.2.1 z.2.2) *
            inner ℝ (nBv z.1) (cross z.2.1 z.2.2) else 0) /
          (√(1 - ‖z.1‖ ^ 2 / 4) * √(1 - ‖z.1 - e‖ ^ 2 / 4))
      else 0) := by
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
  have hNA : Measurable (fun z : Pt × (Pt × Pt) => nAv z.1) := by
    unfold nAv
    fun_prop
  have hNB : Measurable (fun z : Pt × (Pt × Pt) => nBv z.1) := by
    unfold nBv
    fun_prop
  have hcross : Measurable (fun z : Pt × (Pt × Pt) => cross z.2.1 z.2.2) := by
    unfold cross crossProduct
    fun_prop
  have hx : Measurable (fun z : Pt × (Pt × Pt) => inner ℝ z.2.1 z.2.2) :=
    measurable_snd.fst.inner measurable_snd.snd
  have hRho : Measurable (rhoK f) := by
    cases f <;> unfold rhoK <;> fun_prop
  have hcut : Measurable (fun z : Pt × (Pt × Pt) =>
      if 1 / 2 < inner ℝ z.2.1 z.2.2 then
        rhoK f (inner ℝ z.2.1 z.2.2) * inner ℝ (nAv z.1) (cross z.2.1 z.2.2) *
          inner ℝ (nBv z.1) (cross z.2.1 z.2.2) else 0) :=
    (((hRho.comp hx).mul (hNA.inner hcross)).mul (hNB.inner hcross)).ite
      (measurableSet_lt measurable_const hx) measurable_const
  have hden : Measurable (fun z : Pt × (Pt × Pt) =>
      √(1 - ‖z.1‖ ^ 2 / 4) * √(1 - ‖z.1 - e‖ ^ 2 / 4)) := by
    fun_prop
  exact (hcut.div hden).ite
    ((hA.preimage (measurable_fst.prodMk measurable_snd.fst)).inter
      (hB.preimage (measurable_fst.prodMk measurable_snd.snd))) measurable_const
