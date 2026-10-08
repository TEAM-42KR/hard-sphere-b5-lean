import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_AA_chart_stronglyMeasurable
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.AA_chart_stronglyMeasurable :
    ∀ (f : Kern) (p : Pt × ℝ → Pt) (hp : Measurable p) (r : Pt → ℝ) (hr : Measurable r), StronglyMeasurable (fun D : Pt => (1 / 2 : ℝ) * (r D) ^ 2 * ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π), if p (D, t) ∈ arcA D ∧ p (D, s) ∈ arcA D then cutKern f (arccos (inner ℝ (p (D, t)) (p (D, s)))) * santaloDens (p (D, t)) (p (D, s)) (tanA D (p (D, t))) (tanA D (p (D, s))) else 0) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_AA_chart_stronglyMeasurable
