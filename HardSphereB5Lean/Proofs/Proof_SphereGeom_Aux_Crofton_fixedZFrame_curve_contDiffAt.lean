import HardSphereB5Lean.Definitions.Def_SphereGeom_fixedZFrame
set_option autoImplicit false

open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_fixedZFrame_curve_contDiffAt (γ : ℝ → E3) (hγ : ContDiff ℝ 1 γ) (t : ℝ)
    (hQ : (γ t) 0 ^ 2 + (γ t) 1 ^ 2 ≠ 0) :
    ContDiffAt ℝ 1 (fun s => fixedZA (γ s)) t ∧
      ContDiffAt ℝ 1 (fun s => fixedZB (γ s)) t := by
  have hc (i : Fin 3) : ContDiffAt ℝ 1 (fun s => (γ s) i) t :=
    (contDiffAt_euclidean.mp hγ.contDiffAt) i
  have hq : ContDiffAt ℝ 1 (fun s => (γ s) 0 ^ 2 + (γ s) 1 ^ 2) t :=
    ((hc 0).pow 2).add ((hc 1).pow 2)
  have hr : ContDiffAt ℝ 1 (fun s => fixedZRadius (γ s)) t := hq.sqrt hQ
  have hr2 : fixedZRadius (γ t) ^ 2 = (γ t) 0 ^ 2 + (γ t) 1 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hr0 : fixedZRadius (γ t) ≠ 0 := by
    intro hh
    rw [hh] at hr2
    simp at hr2
    exact hQ hr2.symm
  constructor
  · apply contDiffAt_euclidean.mpr
    intro i
    fin_cases i
    · exact (hc 1).neg.div hr hr0
    · exact (hc 0).div hr hr0
    · exact contDiffAt_const
  · apply contDiffAt_euclidean.mpr
    intro i
    fin_cases i
    · exact ((hc 2).neg.mul (hc 0)).div hr hr0
    · exact ((hc 2).neg.mul (hc 1)).div hr hr0
    · exact hr
