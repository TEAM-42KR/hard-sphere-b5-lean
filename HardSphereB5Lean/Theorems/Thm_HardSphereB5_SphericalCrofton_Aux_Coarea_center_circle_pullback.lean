import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_pullback
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.center_circle_pullback :
    ∀ (p p' : Pt)
    (hd : p'-p ≠ 0) (hf : centerFrame0 (p'-p) ≠ 0)
    (g : Pt → ℝ) (hg : Measurable g), (∫ q in {q : Pt | ‖q‖ = 1 ∧ inner ℝ q (p'-p) = 0 ∧
        midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) • q ∈ LamC},
      g (midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) • q) ∂arcMeasure) =
    ∫ ψ in Set.Icc (-Real.pi) Real.pi,
      if midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) •
        (Real.cos ψ • centerFrame0 (p'-p) + Real.sin ψ • centerFrame1 (p'-p)) ∈ LamC
      then g (midpoint ℝ p p' + Real.sqrt (1-dist p p'^2/4) •
        (Real.cos ψ • centerFrame0 (p'-p) + Real.sin ψ • centerFrame1 (p'-p))) else 0 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_center_circle_pullback
