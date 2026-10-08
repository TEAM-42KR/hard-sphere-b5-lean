import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_lensVolFormula
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean

theorem HardSphereB5.Lean.Geometry.lensVolFormula :
    ∀ (l : ℝ) (h0 : 0 ≤ l) (h2 : l ≤ 2), lensVol l = π / 12 * (2 - l) ^ 2 * (4 + l) :=
  @proof_HardSphereB5_Lean_Geometry_lensVolFormula
