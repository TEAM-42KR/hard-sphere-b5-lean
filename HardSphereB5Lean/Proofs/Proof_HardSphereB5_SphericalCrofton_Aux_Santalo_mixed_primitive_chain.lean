import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_cutoff_primitive_derivatives
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open Filter Set
open scoped Classical Topology

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_primitive_chain (f : Kern) (D : Pt) (C : Charts) (t s : ℝ)
    (hx : inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1) :
    Q12 f D C t s =
      (if delta D C t s < π / 3 then deriv (phiK f) (delta D C t s) else 0) *
        deriv (fun z => delta D C z s) t * deriv (delta D C t) s +
      cutKern f (delta D C t s) * deriv (fun z => deriv (delta D C z) s) t := by
  have hUD (z : ℝ) : DifferentiableAt ℝ (u D C) z := by
    unfold u circlePt
    fun_prop
  have hVD (z : ℝ) : DifferentiableAt ℝ (v D C) z := by
    unfold v circlePt
    fun_prop
  let X : ℝ → ℝ := fun z => inner ℝ (u D C z) (v D C s)
  let Y : ℝ → ℝ := fun z => inner ℝ (u D C z) (deriv (v D C) s)
  have hX : HasDerivAt X (inner ℝ (deriv (u D C) t) (v D C s)) t := by
    simpa only [X, inner_zero_right, add_zero, zero_add] using
      (hUD t).hasDerivAt.inner ℝ (hasDerivAt_const t (v D C s))
  have hY : HasDerivAt Y (inner ℝ (deriv (u D C) t) (deriv (v D C) s)) t := by
    simpa only [Y, inner_zero_right, add_zero, zero_add] using
      (hUD t).hasDerivAt.inner ℝ (hasDerivAt_const t (deriv (v D C) s))
  have hXs (z : ℝ) : HasDerivAt (fun q => inner ℝ (u D C z) (v D C q)) (Y z) s := by
    simpa only [Y, inner_zero_left, zero_add, add_zero] using
      (hasDerivAt_const s (u D C z)).inner ℝ (hVD s).hasDerivAt
  have hnb : ∀ᶠ z in 𝓝 t, X z ∈ Set.Ioo (-1) 1 :=
    hX.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hx)
  have hds (z : ℝ) (hz : X z ∈ Set.Ioo (-1) 1) :
      HasDerivAt (delta D C z) (-Y z / Real.sqrt (1 - X z ^ 2)) s := by
    change HasDerivAt (fun q => Real.arccos (inner ℝ (u D C z) (v D C q)))
      (-Y z / Real.sqrt (1 - X z ^ 2)) s
    have hd := (Real.hasDerivAt_arccos (ne_of_gt hz.1) (ne_of_lt hz.2)).comp s (hXs z)
    simpa [X, Y, Function.comp_def, neg_div, div_eq_mul_inv, mul_comm] using hd
  have heqS : (fun z => deriv (delta D C z) s) =ᶠ[𝓝 t]
      (fun z => -Y z / Real.sqrt (1 - X z ^ 2)) := by
    filter_upwards [hnb] with z hz
    exact (hds z hz).deriv
  have hpositive : 0 < 1 - X t ^ 2 := by
    change 0 < 1 - (inner ℝ (u D C t) (v D C s)) ^ 2
    nlinarith [hx.1, hx.2]
  have hDS : DifferentiableAt ℝ (fun z => deriv (delta D C z) s) t := by
    have hdS := (hasDerivAt_const t (1 : ℝ)).sub (hX.pow 2)
    have hdr := hdS.sqrt (ne_of_gt hpositive)
    have hdRatio := hY.neg.div hdr (ne_of_gt (Real.sqrt_pos.mpr hpositive))
    exact (hdRatio.congr_of_eventuallyEq heqS).differentiableAt
  have hDT : HasDerivAt (fun z => delta D C z s)
      (deriv (fun z => delta D C z s) t) t := by
    have hd := (Real.hasDerivAt_arccos (ne_of_gt hx.1) (ne_of_lt hx.2)).comp t hX
    have hdiff : DifferentiableAt ℝ (fun z => delta D C z s) t := by
      simpa only [Function.comp_def, X, delta] using hd.differentiableAt
    exact hdiff.hasDerivAt
  have heqQ2 : (fun z => Q2 f D C z s) =ᶠ[𝓝 t]
      (fun z => cutKern f (delta D C z s) * deriv (delta D C z) s) := by
    filter_upwards [hnb] with z hz
    have hd := (hds z hz).differentiableAt.hasDerivAt
    have hp := (HardSphereB5.SphericalCrofton.Aux.Santalo.cutoff_primitive_derivatives f (delta D C z s)).1
    change deriv (fun q => Pprim f (min (delta D C z q) (π / 3))) s = _
    simpa only [Function.comp_def] using (hp.comp s hd).deriv
  have hcut := (HardSphereB5.SphericalCrofton.Aux.Santalo.cutoff_primitive_derivatives f (delta D C t s)).2.comp t hDT
  have hprod := hcut.mul hDS.hasDerivAt
  have hactual := hprod.congr_of_eventuallyEq heqQ2
  exact hactual.deriv
