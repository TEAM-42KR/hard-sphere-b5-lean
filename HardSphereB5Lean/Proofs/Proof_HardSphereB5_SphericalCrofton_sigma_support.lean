import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_sigma_gram_data
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_gram_obstruction
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_gram_vertices
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_gram_interior
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SurfaceArea_interior_pos
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_sigma_support (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D) :
    (Rc ‖D‖ ‖D - e‖ < 1 → 0 < sArea (SigmaD D) ∧ ∃ V W, V ≠ W ∧ vertsD D = {V, W}) ∧
      (Rc ‖D‖ ‖D - e‖ = 1 → ∃ V, SigmaD D = {V}) ∧
      (1 < Rc ‖D‖ ‖D - e‖ → SigmaD D = ∅) := by
  let x := nAv D
  let y := nBv D
  let a := ‖D‖ / 2
  let b := ‖D - e‖ / 2
  let c := inner ℝ x y
  obtain ⟨hx, hy, hd, ha, hb, hac, hbc, hq, hr, hK, hV⟩ := Aux.Geom.sigma_gram_data D hD hoff
  change ‖x‖ = 1 at hx
  change ‖y‖ = 1 at hy
  change 0 < 1 - c ^ 2 at hd
  change 0 < a at ha
  change 0 < b at hb
  change 0 ≤ a - c * b at hac
  change 0 ≤ b - c * a at hbc
  change (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) = _ at hq
  change SigmaD D = {u : Pt | ‖u‖ = 1 ∧ a ≤ inner ℝ x u ∧ b ≤ inner ℝ y u} at hK
  change vertsD D = {u : Pt | ‖u‖ = 1 ∧ inner ℝ x u = a ∧ inner ℝ y u = b} at hV
  have hxy : inner ℝ x y = c := Eq.refl c
  have hobs := Aux.Geom.gram_obstruction x y a b c hx hy hxy hd hac hbc
  refine ⟨?_, ?_, ?_⟩
  · intro hlt
    have hq1 : (a ^ 2 - 2 * c * a * b + b ^ 2) / (1 - c ^ 2) < 1 := by rw [hq]; nlinarith
    constructor
    · have hi := Aux.Geom.gram_interior x y a b c hx hy hxy hd ha hb hq1
      rw [← hK] at hi
      have hcl : IsClosed (SigmaD D) := by
        rw [hK]
        have hcx : Continuous (fun u : Pt => inner ℝ x u) := continuous_const.inner continuous_id
        have hcy : Continuous (fun u : Pt => inner ℝ y u) := continuous_const.inner continuous_id
        exact (isClosed_eq continuous_norm continuous_const).inter
          ((isClosed_le continuous_const hcx).inter (isClosed_le continuous_const hcy))
      apply SphereGeom.Aux.SurfaceArea.interior_pos _ hcl.measurableSet
      exact Set.image_nonempty.mp hi
    · rw [hV]
      exact Aux.Geom.gram_vertices x y a b c hx hy hxy hd hq1
  · intro heq
    refine ⟨((a - c * b) / (1 - c ^ 2)) • x + ((b - c * a) / (1 - c ^ 2)) • y, ?_⟩
    rw [hK]
    apply hobs.2.1
    rw [hq, heq]
    norm_num
  · intro hgt
    rw [hK]
    apply hobs.2.2
    rw [hq]
    nlinarith
