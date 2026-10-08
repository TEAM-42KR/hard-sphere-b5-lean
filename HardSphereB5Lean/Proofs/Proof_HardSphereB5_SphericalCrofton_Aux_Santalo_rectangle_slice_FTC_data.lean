import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_cutoff_primitive_derivatives
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_primitive_differentiability_at
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_angular_first_derivatives_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_distance_sine_bound
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_primitive_chain
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)
open Set Filter
open scoped Classical Topology

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

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_rectangle_slice_FTC_data (f : Kern) (D : Pt) (C : Charts) (hD : D ∈ LamC)
    (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1) (hC : IsChart D C)
    (hRange : ∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB,
      ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) →
        inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1) :
    (∀ s ∈ Set.Ioo 0 C.TB, ContinuousOn (fun t => Q2 f D C t s) (Set.Icc 0 C.TA)) ∧
    (∀ s ∈ Set.Ioo 0 C.TB, ∀ t ∈ Set.Ioo 0 C.TA,
      HasDerivAt (fun z => Q2 f D C z s) (Q12 f D C t s) t) ∧
    (∀ s ∈ Set.Ioo 0 C.TB, IntervalIntegrable (fun t => Q12 f D C t s) volume 0 C.TA) ∧
    (∀ t ∈ ({0,C.TA} : Set ℝ), ContinuousOn (Q f D C t) (Set.Icc 0 C.TB)) ∧
    (∀ t ∈ ({0,C.TA} : Set ℝ), ∀ s ∈ Set.Ioo 0 C.TB,
      HasDerivAt (Q f D C t) (Q2 f D C t s) s) ∧
    (∀ t ∈ ({0,C.TA} : Set ℝ), IntervalIntegrable (Q2 f D C t) volume 0 C.TB) := by
  have hCc := hC
  rcases hCc with ⟨_,_,_,_,hTA,hTB,_,_,_,_,_,_⟩
  have hrange (t : ℝ) (ht : t ∈ Icc 0 C.TA) (s : ℝ) (hs : s ∈ Ioo 0 C.TB) :
      inner ℝ (u D C t) (v D C s) ∈ Ioo (-1) 1 := by
    apply hRange t ht s ⟨hs.1.le,hs.2.le⟩
    rintro (⟨_,hz⟩ | ⟨_,hz⟩)
    · exact (ne_of_gt hs.1) hz
    · exact (ne_of_lt hs.2) hz
  have hedge (t : ℝ) (ht : t ∈ ({0,C.TA} : Set ℝ)) : t ∈ Icc 0 C.TA := by
    rcases ht with ht | ht
    · subst t; exact ⟨le_rfl,hTA.le⟩
    · have ht' : t = C.TA := ht
      subst t; exact ⟨hTA.le,le_rfl⟩
  have hdeltaT (s : ℝ) : Continuous (fun t => delta D C t s) := by
    unfold delta u v circlePt
    fun_prop
  have hdeltaS (t : ℝ) : Continuous (delta D C t) := by
    change Continuous (fun s => Real.arccos (inner ℝ (u D C t) (v D C s)))
    unfold u v circlePt
    fun_prop
  have hdmem (t s : ℝ) : delta D C t s ∈ Icc 0 Real.pi :=
    ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩
  have hcut : Continuous (cutKern f) :=
    continuous_iff_continuousAt.mpr (fun z => (cutoff_primitive_derivatives f z).2.continuousAt)
  have hP : Continuous (fun z : ℝ => Pprim f (min z (Real.pi/3))) :=
    continuous_iff_continuousAt.mpr (fun z => (cutoff_primitive_derivatives f z).1.continuousAt)
  have hQ (t : ℝ) : Continuous (Q f D C t) := by
    change Continuous (fun s => Pprim f (min (delta D C t s) (Real.pi/3)))
    exact hP.comp (hdeltaS t)
  have hQ2 (t s : ℝ) (hx : inner ℝ (u D C t) (v D C s) ∈ Ioo (-1) 1) :
      Q2 f D C t s = cutKern f (delta D C t s) * deriv (delta D C t) s := by
    have hVD : DifferentiableAt ℝ (v D C) s := by unfold v circlePt; fun_prop
    have hdX := (hasDerivAt_const s (u D C t)).inner ℝ hVD.hasDerivAt
    have hd := (Real.hasDerivAt_arccos (ne_of_gt hx.1) (ne_of_lt hx.2)).comp s hdX
    have hdiff : DifferentiableAt ℝ (delta D C t) s := by
      change DifferentiableAt ℝ (fun z => Real.arccos (inner ℝ (u D C t) (v D C z))) s
      simpa only [Function.comp_def] using hd.differentiableAt
    have hp := (cutoff_primitive_derivatives f (delta D C t s)).1.comp s hdiff.hasDerivAt
    change deriv (fun z => Pprim f (min (delta D C t z) (Real.pi/3))) s = _
    simpa only [Function.comp_def] using hp.deriv
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcut.continuousOn
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn (phi_deriv_continuous f).continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl,Real.pi_pos.le⟩)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 ⟨le_rfl,Real.pi_pos.le⟩)
  have hcutBound (t s : ℝ) : |cutKern f (delta D C t s)| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB (delta D C t s) (hdmem t s)
  have hdcBound (t s : ℝ) :
      |if delta D C t s < Real.pi/3 then deriv (phiK f) (delta D C t s) else 0| ≤ A := by
    split_ifs
    · simpa only [Real.norm_eq_abs] using hA (delta D C t s) (hdmem t s)
    · simpa using hA0
  have hQ12int (s : ℝ) (hs : s ∈ Ioo 0 C.TB) :
      IntervalIntegrable (fun t => Q12 f D C t s) volume 0 C.TA := by
    have hinv : ContinuousOn (fun t => (Real.sin (delta D C t s))⁻¹) (Icc 0 C.TA) := by
      apply ((Real.continuous_sin.comp (hdeltaT s)).continuousOn).inv₀
      intro t ht
      have hx := hrange t ht s hs
      have hpos : 0 < 1 - (inner ℝ (u D C t) (v D C s))^2 := by nlinarith [hx.1,hx.2]
      change Real.sin (Real.arccos (inner ℝ (u D C t) (v D C s))) ≠ 0
      rw [Real.sin_arccos]
      exact ne_of_gt (Real.sqrt_pos.mpr hpos)
    obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hinv
    have hKB (t : ℝ) (ht : t ∈ Icc 0 C.TA) : (Real.sin (delta D C t s))⁻¹ ≤ K := by
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hK t ht)
    have hbound (t : ℝ) (ht : t ∈ Icc 0 C.TA) : |Q12 f D C t s| ≤ A+B*K := by
      have hx := hrange t ht s hs
      have hfirst := angular_first_derivatives_bound D C hD hoff hC t s ht ⟨hs.1.le,hs.2.le⟩ hx
      have hmixed := (mixed_distance_sine_bound D C hD hoff hR hC t s ht ⟨hs.1.le,hs.2.le⟩ hx).trans (hKB t ht)
      have hb1 : |(if delta D C t s < Real.pi/3 then deriv (phiK f) (delta D C t s) else 0) *
          deriv (fun z => delta D C z s) t * deriv (delta D C t) s| ≤ A := by
        rw [abs_mul,abs_mul]
        calc
          _ ≤ (A*1)*1 := mul_le_mul
            (mul_le_mul (hdcBound t s) hfirst.1 (abs_nonneg _) hA0)
            hfirst.2 (abs_nonneg _) (by positivity)
          _ = A := by ring
      have hb2 : |cutKern f (delta D C t s) * deriv (fun z => deriv (delta D C z) s) t| ≤ B*K := by
        rw [abs_mul]
        exact mul_le_mul (hcutBound t s) hmixed (abs_nonneg _) hB0
      rw [mixed_primitive_chain f D C t s hx]
      refine le_trans ?_ (add_le_add hb1 hb2)
      simpa only [Real.norm_eq_abs] using norm_add_le
        ((if delta D C t s < Real.pi/3 then deriv (phiK f) (delta D C t s) else 0) *
          deriv (fun z => delta D C z s) t * deriv (delta D C t) s)
        (cutKern f (delta D C t s) * deriv (fun z => deriv (delta D C z) s) t)
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hTA.le).mpr
    change Integrable (fun t => Q12 f D C t s) (volume.restrict (Icc 0 C.TA))
    refine (integrable_const (A+B*K)).mono' ?_ ?_
    · exact (measurable_deriv (fun t => Q2 f D C t s)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simpa only [Real.norm_eq_abs] using hbound t ht
  have hQ2int (t : ℝ) (ht : t ∈ ({0,C.TA} : Set ℝ)) :
      IntervalIntegrable (Q2 f D C t) volume 0 C.TB := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hTB.le).mpr
    change Integrable (Q2 f D C t) (volume.restrict (Ioo 0 C.TB))
    refine (integrable_const B).mono' ?_ ?_
    · exact (measurable_deriv (Q f D C t)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hx := hrange t (hedge t ht) s hs
      have hb := (angular_first_derivatives_bound D C hD hoff hC t s
        (hedge t ht) ⟨hs.1.le,hs.2.le⟩ hx).2
      rw [Real.norm_eq_abs,hQ2 t s hx,abs_mul]
      simpa only [mul_one] using mul_le_mul (hcutBound t s) hb (abs_nonneg _) hB0
  refine ⟨?_,?_,hQ12int,?_,?_,hQ2int⟩
  · intro s hs t ht
    exact (primitive_differentiability_at f D C t s (hrange t ht s hs)).2.continuousAt.continuousWithinAt
  · intro s hs t ht
    exact (primitive_differentiability_at f D C t s (hrange t ⟨ht.1.le,ht.2.le⟩ s hs)).2
  · intro t ht
    exact (hQ t).continuousOn
  · intro t ht s hs
    exact (primitive_differentiability_at f D C t s (hrange t (hedge t ht) s hs)).1
