import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

private lemma measurable_cross : Measurable (fun z : Pt × Pt => cross z.1 z.2) := by
  unfold cross crossProduct
  fun_prop

private lemma measurable_ab (f : Kern) (D : Pt) : Measurable (Function.uncurry (abKernel f D)) := by
  have hc : Measurable (fun z : Pt × Pt => cross z.1 z.2) := measurable_cross
  have hcA : Measurable (fun z : Pt × Pt => cross (nAv D) z.1) :=
    measurable_cross.comp (measurable_const.prodMk measurable_fst)
  have hcB : Measurable (fun z : Pt × Pt => cross (nBv D) z.2) :=
    measurable_cross.comp (measurable_const.prodMk measurable_snd)
  have hcut : Measurable (cutKern f) := by
    have hs : MeasurableSet {L : ℝ | L < π / 3} := measurableSet_lt measurable_id measurable_const
    cases f
    · change Measurable (fun L : ℝ => if L < π / 3 then L - 2 * sin L + √3 - π / 3 else 0)
      exact (by fun_prop : Measurable (fun L : ℝ => L - 2 * sin L + √3 - π / 3)).ite hs measurable_const
    · change Measurable (fun L : ℝ => if L < π / 3 then π / 12 + √3 / 8 - L / 4 - sin (2 * L) / 4 else 0)
      exact (by fun_prop : Measurable (fun L : ℝ => π / 12 + √3 / 8 - L / 4 - sin (2 * L) / 4)).ite hs measurable_const
  have htanA : Measurable (fun z : Pt × Pt => tanA D z.1) := by
    unfold tanA unitDir; fun_prop
  have htanB : Measurable (fun z : Pt × Pt => tanB D z.2) := by
    unfold tanB unitDir; fun_prop
  have hcutcomp : Measurable (fun z : Pt × Pt => cutKern f (arccos (inner ℝ z.1 z.2))) :=
    hcut.comp (by fun_prop)
  unfold Function.uncurry abKernel santaloDens
  fun_prop

private lemma measurable_b (f : Kern) (D : Pt) : Measurable (Function.uncurry (bKernel f D)) := by
  have hc : Measurable (fun z : Pt × Pt => cross z.1 z.2) := measurable_cross
  have hmain : Measurable (fun z : Pt × Pt => rhoK f (inner ℝ z.1 z.2) *
      inner ℝ (nAv D) (cross z.1 z.2) * inner ℝ (nBv D) (cross z.1 z.2)) := by
    cases f <;> simp only [rhoK] <;> fun_prop
  have hx : Measurable (fun z : Pt × Pt => inner ℝ z.1 z.2) := by fun_prop
  have hs : MeasurableSet {z : Pt × Pt | (1 / 2 : ℝ) < inner ℝ z.1 z.2} :=
    measurableSet_lt measurable_const hx
  exact (hmain.ite hs measurable_const).div_const (rA D * rB D)

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_measurable_kernels (f : Kern) (D : Pt) : Measurable (Function.uncurry (abKernel f D)) ∧ Measurable (Function.uncurry (bKernel f D)) := by
  exact ⟨measurable_ab f D, measurable_b f D⟩
