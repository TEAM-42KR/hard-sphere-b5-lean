import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_measurable_frame
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_AA_chart_stronglyMeasurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_AA_circle_chart_formula
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
set_option maxHeartbeats 600000

theorem proof_HardSphereB5_SphericalCrofton_Aux_AAf_aestronglyMeasurable (f : Kern) : AEStronglyMeasurable (AAf f) (volume.restrict LamC) := by
  obtain ⟨F1, F2, hF1, hF2, hF⟩ := SphereGeom.exists_measurable_frame
  let r : Pt → ℝ := fun D => Real.sqrt (1 - ‖D‖ ^ 2 / 4)
  let p : Pt × ℝ → Pt := fun z =>
    circlePt ((-(1 / 2 : ℝ)) • z.1) (F1 (nAv z.1)) (F2 (nAv z.1)) (r z.1) z.2
  have hnmeas : Measurable nAv := by unfold nAv; fun_prop
  have hr : Measurable r := by dsimp [r]; fun_prop
  have hp : Measurable p := by dsimp [p]; unfold circlePt; fun_prop
  let G : Pt → ℝ := fun D => (1 / 2 : ℝ) * (r D) ^ 2 *
    ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π),
      if p (D, t) ∈ arcA D ∧ p (D, s) ∈ arcA D then
        cutKern f (arccos (inner ℝ (p (D, t)) (p (D, s)))) *
          santaloDens (p (D, t)) (p (D, s)) (tanA D (p (D, t))) (tanA D (p (D, s))) else 0
  have hG : StronglyMeasurable G := AA_chart_stronglyMeasurable f p hp r hr
  apply hG.aestronglyMeasurable.congr
  have hLam : MeasurableSet LamC := by
    exact measurableSet_closedBall.inter measurableSet_closedBall
  filter_upwards [ae_restrict_mem hLam] with D hD
  by_cases h0 : D = 0
  · subst D
    simp [G, AAf, arcA]
  · have hn : ‖nAv D‖ = 1 := by
      simp [nAv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg D),
        norm_ne_zero_iff.mpr h0, inv_mul_cancel₀]
    simpa [G, p, r] using
      (AA_circle_chart_formula f D hD h0 ![F1 (nAv D), F2 (nAv D), nAv D] (hF _ hn) rfl).symm
