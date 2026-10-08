import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_transverse_local_distance
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_vertex_transversality
set_option autoImplicit false
noncomputable section
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo Filter
open HardSphereB5.Lean (Pt e)
open scoped Topology

private lemma cross_neg_right (a b : Pt) : cross a (-b) = -cross a b := by
  ext i; fin_cases i <;> simp [cross, cross_apply] <;> ring

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_chart_local_distance (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) (hC : IsChart D C) (a b : ℝ)
    (heq : u D C a = v D C b) (hv : u D C a ∈ vertsD D) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℝ × ℝ in 𝓝 (a, b),
      c * ‖z - (a, b)‖ ≤ ‖u D C z.1 - v D C z.2‖ := by
  rcases hC with ⟨_, _, _, _, _, _, _, _, _, _, hdu, hdv⟩
  have htrans := HardSphereB5.SphericalCrofton.Aux.Santalo.vertex_transversality D (u D C a) hD hoff hR hv
  have hcross : cross (cross (nAv D) (u D C a)) (-cross (nBv D) (v D C b)) ≠ 0 := by
    rw [← heq, cross_neg_right]
    exact neg_ne_zero.mpr htrans
  exact SphereGeom.Aux.Santalo.transverse_local_distance (u D C) (v D C)
    (cross (nAv D) (u D C a)) (-cross (nBv D) (v D C b)) a b (hdu a) (hdv b) heq hcross
