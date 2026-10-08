import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false

noncomputable section
open Filter

theorem proof_HardSphereB5_Lean_Santalo_santaloMixed (X : ℝ → ℝ → ℝ) (X1 : ℝ → ℝ)
    (s t x2 x12 L1 L2 : ℝ) (hx : X s t ∈ Set.Ioo (-1) 1)
    (h1 : ∀ y, HasDerivAt (fun z => X z y) (X1 y) s)
    (h2 : HasDerivAt (X s) x2 t) (h12 : HasDerivAt X1 x12 t)
    (hGram : (1 - X s t ^ 2) * x12 + X s t * X1 t * x2 = L1 * L2) :
    -deriv (fun y => deriv (fun z => Real.arccos (X z y)) s) t =
      L1 * L2 / ((1 - X s t ^ 2) * Real.sqrt (1 - X s t ^ 2)) := by
  have hS : 0 < 1 - X s t ^ 2 := by nlinarith [hx.1, hx.2]
  have hS0 : 1 - X s t ^ 2 ≠ 0 := ne_of_gt hS
  have hr0 : Real.sqrt (1 - X s t ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hS)
  have hsq : Real.sqrt (1 - X s t ^ 2) ^ 2 = 1 - X s t ^ 2 := Real.sq_sqrt hS.le
  have hnb : ∀ᶠ y in nhds t, X s y ∈ Set.Ioo (-1) 1 :=
    h2.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hx)
  have heq : (fun y => deriv (fun z => Real.arccos (X z y)) s) =ᶠ[nhds t]
      (fun y => -X1 y / Real.sqrt (1 - X s y ^ 2)) := by
    filter_upwards [hnb] with y hy
    have ha := (Real.hasDerivAt_arccos (ne_of_gt hy.1) (ne_of_lt hy.2)).comp s (h1 y)
    simpa [Function.comp_def, neg_div, div_eq_mul_inv, mul_comm] using ha.deriv
  have hdS := (hasDerivAt_const t (1 : ℝ)).sub (h2.pow 2)
  have hdr := hdS.sqrt hS0
  have hdq := h12.neg.div hdr hr0
  have hd := hdq.congr_of_eventuallyEq heq
  rw [hd.deriv]
  norm_num
  field_simp [hr0, hS0]
  rw [hsq]
  nlinarith [hGram]
