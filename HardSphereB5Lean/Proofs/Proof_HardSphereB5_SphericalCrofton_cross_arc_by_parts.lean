import Mathlib
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_measurable_kernels
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_canonical_closed_density_chain_rule
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_rectangle_regular_canonical
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_kernel_transport
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_rectangle_FTC
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_cross_arc_by_parts (f : Kern) (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) :
    ABf f D = 2 * Pprim f (min (deltaV D) (π / 3)) + Bf f D := by
  obtain ⟨C, hC, hdd, hd0, h0d, h00, hrange, hchainAll⟩ := canonical_closed_density_chain_rule D hD hoff hR
  have hspans : 0 ≤ C.TA ∧ 0 ≤ C.TB := by
    rcases hC with ⟨_, _, _, _, hA, hB, _, _, _, _, _, _⟩
    exact ⟨hA.le, hB.le⟩
  rcases rectangle_regular_canonical f D C hD hoff hR hC h00 hdd hrange with
    ⟨hQprod, hHprod, hcont, hderiv, hint, hedge, hDedge, hIedge⟩
  have hFTC := SphereGeom.Aux.Santalo.rectangle_FTC (Q f D C) (Q2 f D C)
    (Q12 f D C) 0 C.TA 0 C.TB hspans.1 hspans.2 hQprod
    hcont hderiv hint hedge hDedge hIedge
  have hJ : ABf f D = ∫ t in (0 : ℝ)..C.TA, ∫ s in (0 : ℝ)..C.TB, J f D C t s := by
    exact kernel_transport D C hC (abKernel f D) (measurable_kernels f D).1
  have hH : Bf f D = ∫ t in (0 : ℝ)..C.TA, ∫ s in (0 : ℝ)..C.TB, H f D C t s := by
    exact kernel_transport D C hC (bKernel f D) (measurable_kernels f D).2
  have hchain : ∀ t ∈ Set.Ioo 0 C.TA, ∀ s ∈ Set.Ioo 0 C.TB,
      J f D C t s = -Q12 f D C t s + H f D C t s := by
    intro t ht s hs
    apply hchainAll f t ⟨ht.1.le,ht.2.le⟩ s ⟨hs.1.le,hs.2.le⟩
    rintro (h|h)
    · exact (ne_of_gt ht.1) h.1
    · exact (ne_of_lt ht.2) h.1
  have hJI : (∫ t in (0 : ℝ)..C.TA, ∫ s in (0 : ℝ)..C.TB, J f D C t s) =
      ∫ t in (0 : ℝ)..C.TA, ∫ s in (0 : ℝ)..C.TB, -Q12 f D C t s + H f D C t s := by
    simp_rw [intervalIntegral.integral_of_le hspans.1, intervalIntegral.integral_of_le hspans.2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae ((volume : Measure ℝ).ae_ne C.TA)] with t ht htne
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae ((volume : Measure ℝ).ae_ne C.TB)] with s hs hsne
    exact hchain t ⟨ht.1, lt_of_le_of_ne ht.2 htne⟩ s ⟨hs.1, lt_of_le_of_ne hs.2 hsne⟩
  have hsplit : (∫ t in (0 : ℝ)..C.TA, ∫ s in (0 : ℝ)..C.TB, -Q12 f D C t s + H f D C t s) =
      -(∫ t in (0 : ℝ)..C.TA, ∫ s in (0 : ℝ)..C.TB, Q12 f D C t s) +
        (∫ t in (0 : ℝ)..C.TA, ∫ s in (0 : ℝ)..C.TB, H f D C t s) := by
    simp_rw [intervalIntegral.integral_of_le hspans.1, intervalIntegral.integral_of_le hspans.2]
    rw [integral_integral (hQprod.neg.add hHprod)]
    have hadd := integral_add hQprod.neg hHprod
    simp only [Pi.add_apply, Pi.neg_apply, Function.uncurry] at hadd
    rw [integral_neg] at hadd
    rw [hadd, ← integral_integral hQprod, ← integral_integral hHprod]
  have hpi : (0 : ℝ) ≤ π / 3 := by positivity
  have hcorners : Q f D C C.TA C.TB - Q f D C C.TA 0 - Q f D C 0 C.TB + Q f D C 0 0 =
      -2 * Pprim f (min (deltaV D) (π / 3)) := by
    simp only [Q, hdd, hd0, h0d, h00, min_eq_left hpi, Pprim, intervalIntegral.integral_same]
    ring
  rw [hJ, hJI, hsplit, hFTC, hcorners, ← hH]
  ring
