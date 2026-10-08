import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_frontier_active
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Geom.cap_frontier_active :
    ∀ (N : ℕ) (hN : 0 < N) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m)
    (hint : (sInterior (⋂ m, cap (n m) (h m))).Nonempty), sFrontier (⋂ m, cap (n m) (h m)) = ⋃ m, ((⋂ i, cap (n i) (h i)) ∩ {u : Pt | inner ℝ (n m) u = h m}) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_frontier_active
