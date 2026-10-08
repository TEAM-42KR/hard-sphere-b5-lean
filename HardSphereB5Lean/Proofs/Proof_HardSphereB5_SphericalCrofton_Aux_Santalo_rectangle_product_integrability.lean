import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_inverse_sine_rectangle_integrable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_measurable_kernels
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_density_chain_rule_at
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_bKernel_uniform_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_primitive_chain
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_angular_first_derivatives_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_distance_sine_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_cutoff_primitive_derivatives
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo Filter
open HardSphereB5.Lean (Pt e)
open scoped Topology

private theorem phi_deriv_continuous (f : Kern) : Continuous (deriv (phiK f)) := by
  cases f with
  | one =>
    have hd (x : ℝ) : HasDerivAt (phiK .one) (1 - 2 * Real.cos x) x := by
      convert (((hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).const_mul 2)).add_const
        (Real.sqrt 3)).sub_const (Real.pi / 3) using 1 <;> first | rfl | ring
    rw [show deriv (phiK .one) = (fun x => 1 - 2 * Real.cos x) from funext (fun x => (hd x).deriv)]
    fun_prop
  | cos =>
    have hd (x : ℝ) : HasDerivAt (phiK .cos) (1 / 4 - Real.cos x ^ 2) x := by
      convert ((hasDerivAt_const x (Real.pi / 12 + Real.sqrt 3 / 8)).sub
        ((hasDerivAt_id x).div_const 4)).sub
        ((((hasDerivAt_id x).const_mul 2).sin).div_const 4) using 1 <;>
        first | rfl | (simp only [Real.cos_two_mul, id_eq]; ring)
    rw [show deriv (phiK .cos) = (fun x => 1 / 4 - Real.cos x ^ 2) from funext (fun x => (hd x).deriv)]
    fun_prop

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_rectangle_product_integrability (f : Kern) (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D-e‖ < 1) (hC : IsChart D C)
    (h00 : delta D C 0 0 = 0) (hdd : delta D C C.TA C.TB = 0)
    (hrange : ∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB,
      ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) →
      inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1) :
    Integrable (Function.uncurry (Q12 f D C))
      ((volume.restrict (Set.Ioc 0 C.TA)).prod (volume.restrict (Set.Ioc 0 C.TB))) ∧
    Integrable (Function.uncurry (H f D C))
      ((volume.restrict (Set.Ioc 0 C.TA)).prod (volume.restrict (Set.Ioc 0 C.TB))) := by
  let K := Set.Icc 0 C.TA ×ˢ Set.Icc 0 C.TB
  let T := Set.Ioc 0 C.TA ×ˢ Set.Ioc 0 C.TB
  have hsub : T ⊆ K := Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hT : MeasurableSet T := measurableSet_Ioc.prod measurableSet_Ioc
  have htfin : volume T < ⊤ := lt_of_le_of_lt (measure_mono hsub) hK.measure_lt_top
  haveI : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict T) :=
    ⟨by simpa using htfin⟩
  let μ : Measure (ℝ × ℝ) := volume.restrict T
  have hu : Continuous (u D C) := by unfold u circlePt; fun_prop
  have hv : Continuous (v D C) := by unfold v circlePt; fun_prop
  have hmap : Measurable (fun z : ℝ × ℝ => (u D C z.1, v D C z.2)) := by fun_prop
  have hmJ : Measurable (Function.uncurry (J f D C)) := by
    have hg := (measurable_kernels f D).1.comp hmap
    exact (measurable_const.mul measurable_const).mul hg
  have hmH : Measurable (Function.uncurry (H f D C)) := by
    have hg := (measurable_kernels f D).2.comp hmap
    exact (measurable_const.mul measurable_const).mul hg
  have haq : Function.uncurry (Q12 f D C) =ᵐ[μ]
      (fun z => -J f D C z.1 z.2 + H f D C z.1 z.2) := by
    filter_upwards [ae_restrict_mem hT,
      ae_restrict_of_ae ((volume : Measure (ℝ × ℝ)).ae_ne (C.TA,C.TB))] with z hz hne
    have hc : ¬ ((z.1=0 ∧ z.2=0) ∨ (z.1=C.TA ∧ z.2=C.TB)) := by
      rintro (h|h)
      · exact (ne_of_gt hz.1.1) h.1
      · exact hne (Prod.ext h.1 h.2)
    have hx := hrange z.1 ⟨hz.1.1.le,hz.1.2⟩ z.2 ⟨hz.2.1.le,hz.2.2⟩ hc
    have h := density_chain_rule_at f D C hD hoff hR hC z.1 z.2
      ⟨hz.1.1.le,hz.1.2⟩ ⟨hz.2.1.le,hz.2.2⟩ hx
    dsimp [Function.uncurry]; linarith
  have hQmeas : AEStronglyMeasurable (Function.uncurry (Q12 f D C)) μ :=
    (hmJ.neg.add hmH).aestronglyMeasurable.congr haq.symm
  have hHbound : ∀ z ∈ T, ‖H f D C z.1 z.2‖ ≤ 4 := by
    intro z hz
    have hUa : u D C z.1 ∈ arcA D := by
      rw [hC.2.2.2.2.2.2.2.2.1]; exact ⟨z.1,⟨hz.1.1.le,hz.1.2⟩,rfl⟩
    have hVb : v D C z.2 ∈ arcB D := by
      rw [hC.2.2.2.2.2.2.2.2.2.1]; exact ⟨z.2,⟨hz.2.1.le,hz.2.2⟩,rfl⟩
    have hA : 0 ≤ rA D := Real.sqrt_nonneg _
    have hB : 0 ≤ rB D := Real.sqrt_nonneg _
    have hAle : rA D ≤ 1 := by
      dsimp [rA]; exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ‖D‖])
    have hBle : rB D ≤ 1 := by
      dsimp [rB]; exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ‖D-e‖])
    have hspeed : 0 ≤ rA D * rB D := mul_nonneg hA hB
    have hspeed1 : rA D * rB D ≤ 1 := by nlinarith
    rw [H, norm_mul, Real.norm_eq_abs, abs_of_nonneg hspeed]
    calc
      _ ≤ (rA D*rB D)*4 := mul_le_mul_of_nonneg_left
        (bKernel_uniform_bound f D _ _ hD hUa hVb) hspeed
      _ ≤ 4 := by nlinarith
  have hHint : Integrable (Function.uncurry (H f D C)) μ := by
    apply (integrable_const (4 : ℝ)).mono' hmH.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hT] with z hz
    exact hHbound z hz
  have hcut : Continuous (cutKern f) := continuous_iff_continuousAt.mpr
    (fun d => (cutoff_primitive_derivatives f d).2.continuousAt)
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcut.continuousOn
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn (phi_deriv_continuous f).continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl,Real.pi_pos.le⟩)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 ⟨le_rfl,Real.pi_pos.le⟩)
  have hsinI := inverse_sine_rectangle_integrable D C hD hoff hR hC h00 hdd hrange
  have hdomI : Integrable (fun z : ℝ × ℝ => A+B*(Real.sin (delta D C z.1 z.2))⁻¹) μ :=
    (integrable_const A).add ((hsinI.mono_set hsub).const_mul B)
  have hQint : Integrable (Function.uncurry (Q12 f D C)) μ := by
    apply hdomI.mono' hQmeas
    filter_upwards [ae_restrict_mem hT,
      ae_restrict_of_ae ((volume : Measure (ℝ × ℝ)).ae_ne (C.TA,C.TB))] with z hz hne
    have hc : ¬ ((z.1=0 ∧ z.2=0) ∨ (z.1=C.TA ∧ z.2=C.TB)) := by
      rintro (h|h)
      · exact (ne_of_gt hz.1.1) h.1
      · exact hne (Prod.ext h.1 h.2)
    have hx := hrange z.1 ⟨hz.1.1.le,hz.1.2⟩ z.2 ⟨hz.2.1.le,hz.2.2⟩ hc
    have hdmem : delta D C z.1 z.2 ∈ Set.Icc 0 π :=
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    have hb : |cutKern f (delta D C z.1 z.2)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB _ hdmem
    have ha : |if delta D C z.1 z.2 < π/3 then deriv (phiK f) (delta D C z.1 z.2) else 0| ≤ A := by
      split_ifs
      · simpa only [Real.norm_eq_abs] using hA _ hdmem
      · simpa using hA0
    have hf := angular_first_derivatives_bound D C hD hoff hC z.1 z.2
      ⟨hz.1.1.le,hz.1.2⟩ ⟨hz.2.1.le,hz.2.2⟩ hx
    have hm := mixed_distance_sine_bound D C hD hoff hR hC z.1 z.2
      ⟨hz.1.1.le,hz.1.2⟩ ⟨hz.2.1.le,hz.2.2⟩ hx
    have hb1 : |(if delta D C z.1 z.2 < π/3 then deriv (phiK f) (delta D C z.1 z.2) else 0) *
        deriv (fun t => delta D C t z.2) z.1 * deriv (delta D C z.1) z.2| ≤ A := by
      rw [abs_mul,abs_mul]
      calc
        _ ≤ (A*1)*1 := mul_le_mul (mul_le_mul ha hf.1 (abs_nonneg _) hA0)
          hf.2 (abs_nonneg _) (by positivity)
        _ = A := by ring
    have hb2 : |cutKern f (delta D C z.1 z.2) * deriv (fun t => deriv (delta D C t) z.2) z.1| ≤
        B*(Real.sin (delta D C z.1 z.2))⁻¹ := by
      rw [abs_mul]; exact mul_le_mul hb hm (abs_nonneg _) hB0
    simpa only [Real.norm_eq_abs,Function.uncurry] using
      (by rw [mixed_primitive_chain f D C z.1 z.2 hx];
          exact (abs_add_le _ _).trans (add_le_add hb1 hb2) :
        |Q12 f D C z.1 z.2| ≤ A+B*(Real.sin (delta D C z.1 z.2))⁻¹)
  constructor <;> rw [Measure.prod_restrict] <;> first | exact hQint | exact hHint
