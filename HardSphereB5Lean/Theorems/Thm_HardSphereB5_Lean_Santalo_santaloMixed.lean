import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Santalo_santaloMixed
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false

theorem HardSphereB5.Lean.Santalo.santaloMixed :
    ∀ (X : ℝ → ℝ → ℝ) (X1 : ℝ → ℝ) (s t x2 x12 L1 L2 : ℝ) (hx : X s t ∈ Set.Ioo (-1) 1) (h1 : ∀ y, HasDerivAt (fun z => X z y) (X1 y) s) (h2 : HasDerivAt (X s) x2 t) (h12 : HasDerivAt X1 x12 t) (hGram : (1 - X s t ^ 2) * x12 + X s t * X1 t * x2 = L1 * L2), -deriv (fun y => deriv (fun z => Real.arccos (X z y)) s) t = L1 * L2 / ((1 - X s t ^ 2) * Real.sqrt (1 - X s t ^ 2)) :=
  @proof_HardSphereB5_Lean_Santalo_santaloMixed
