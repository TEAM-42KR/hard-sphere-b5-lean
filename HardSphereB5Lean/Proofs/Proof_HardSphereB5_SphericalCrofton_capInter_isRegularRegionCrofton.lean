import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_CapIntersection_basic_properties
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_cap_inter_density
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_cap_boundary_arcs
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_finite_arc_perimeter
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_capInter_isRegularRegionCrofton (N : ℕ) (hN : 0 < N) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m)
    (hint : (sInterior (⋂ m, cap (n m) (h m))).Nonempty) :
    IsRegularRegionCrofton (⋂ m, cap (n m) (h m)) := by
  obtain ⟨hsub, hcomp, hhem, hconv⟩ := SphereGeom.Aux.CapIntersection.basic_properties N hN n h hn h0
  obtain ⟨M, γ, hγ, hinj, hderiv, hfront⟩ := Aux.Geom.cap_boundary_arcs N hN n h hn h0 hint
  refine {
    subset_sphere := hsub
    isCompact := hcomp
    eq_closure_interior := Aux.Geom.cap_inter_density N hN n h hn h0 hint
    interior_nonempty := hint
    geodesically_convex := hconv
    in_closed_hemisphere := hhem
    boundary_C2_arcs := ⟨M, γ, hγ, hinj, hderiv, hfront⟩
    finite_perimeter := by rw [hfront]; exact Aux.Geom.finite_arc_perimeter M γ hγ
  }
