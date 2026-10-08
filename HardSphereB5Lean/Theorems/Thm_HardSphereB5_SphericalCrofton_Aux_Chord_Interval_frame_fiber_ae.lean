import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_frame_fiber_ae
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Chord.Interval.frame_fiber_ae :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern) (F₁ F₂ : Pt → Pt) (hF₁ : Measurable F₁) (hF₂ : Measurable F₂) (hF : ∀ p, ‖p‖ = 1 → Orthonormal ℝ ![F₁ p, F₂ p, p]), ∀ᵐ p ∂dOmega, (∫⁻ t₁ in Set.Ioc 0 (2 * π), ∫⁻ t₂ in Set.Ioc 0 (2 * π), (fun u v : Pt => if u ∈ K ∧ v ∈ K ∧ (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0) (Real.cos t₁ • F₁ p + Real.sin t₁ • F₂ p) (Real.cos t₂ • F₁ p + Real.sin t₂ • F₂ p) * ENNReal.ofReal |Real.sin (t₁ - t₂)|) = ENNReal.ofReal ((fun G => if 0 < chordLen K G then kK f (chordLen K G) else 0) (greatCircle p)) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_frame_fiber_ae
