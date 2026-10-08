import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_capInter_isRegularRegionCrofton
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.capInter_isRegularRegionCrofton :
    ∀ (N : ℕ) (hN : 0 < N) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m)
    (hint : (sInterior (⋂ m, cap (n m) (h m))).Nonempty), IsRegularRegionCrofton (⋂ m, cap (n m) (h m)) :=
  @proof_HardSphereB5_SphericalCrofton_capInter_isRegularRegionCrofton
