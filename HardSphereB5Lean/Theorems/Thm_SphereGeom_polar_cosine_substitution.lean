import HardSphereB5Lean.Proofs.Proof_SphereGeom_polar_cosine_substitution
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem SphereGeom.polar_cosine_substitution :
    ∀ (f : ℝ → ℝ), (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * f (Real.cos θ)) =
 ∫ z in (-1 : ℝ)..1, f z :=
  @proof_SphereGeom_polar_cosine_substitution
