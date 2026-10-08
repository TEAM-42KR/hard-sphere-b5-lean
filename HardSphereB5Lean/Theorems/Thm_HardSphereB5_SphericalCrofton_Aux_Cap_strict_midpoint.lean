import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Cap_strict_midpoint
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Cap.strict_midpoint :
    ∀ (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hpos : ∀ i, 0 < h i) (u v : Pt) (hus : ‖u‖ = 1) (hvs : ‖v‖ = 1)
    (hu : ∀ i, h i ≤ inner ℝ (n i) u) (hv : ∀ i, h i ≤ inner ℝ (n i) v)
    (huv : u ≠ v) (hnon : u ≠ -v), ∃ w : Metric.sphere (0 : Pt) 1, ∀ i, h i < inner ℝ (n i) (w : Pt) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Cap_strict_midpoint
