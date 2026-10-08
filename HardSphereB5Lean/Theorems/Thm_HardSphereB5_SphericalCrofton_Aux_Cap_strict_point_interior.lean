import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Cap_strict_point_interior
import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Cap.strict_point_interior :
    ∀ (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ) (w : Metric.sphere (0 : Pt) 1) (hw : ∀ i, h i < inner ℝ (n i) (w : Pt)), (sInterior (⋂ i, cap (n i) (h i))).Nonempty :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Cap_strict_point_interior
