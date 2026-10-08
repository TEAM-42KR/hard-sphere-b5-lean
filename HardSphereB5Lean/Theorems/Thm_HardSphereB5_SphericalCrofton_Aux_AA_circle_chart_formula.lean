import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_AA_circle_chart_formula
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.AA_circle_chart_formula :
    ∀ (f : Kern) (D : Pt) (hD : D ∈ LamC) (h0 : D ≠ 0) (E : Fin 3 → Pt) (hE : Orthonormal ℝ E) (hn : E 2 = nAv D), AAf f D = (1 / 2 : ℝ) * (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) ^ 2 * ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π), if circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t ∈ arcA D ∧ circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s ∈ arcA D then cutKern f (arccos (inner ℝ (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t) (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s))) * santaloDens (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t) (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s) (tanA D (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) t)) (tanA D (circlePt ((-(1 / 2 : ℝ)) • D) (E 0) (E 1) (Real.sqrt (1 - ‖D‖ ^ 2 / 4)) s)) else 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_AA_circle_chart_formula
