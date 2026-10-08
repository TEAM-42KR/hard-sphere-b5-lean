import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_compact_inverse_integrable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_chart_local_sine
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo Filter
open HardSphereB5.Lean (Pt e)
open scoped Topology

private lemma norm_le_radius (z p : ℝ × ℝ) :
    ‖z - p‖ ≤ Real.sqrt ((z.1-p.1)^2+(z.2-p.2)^2) := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hs := Real.sq_sqrt (show 0 ≤ (z.1-p.1)^2+(z.2-p.2)^2 by positivity)
  have hr := Real.sqrt_nonneg ((z.1-p.1)^2+(z.2-p.2)^2)
  apply max_le <;> simp only [Prod.fst_sub, Prod.snd_sub]
  · nlinarith [sq_abs (z.1-p.1), abs_nonneg (z.1-p.1), sq_nonneg (z.2-p.2)]
  · nlinarith [sq_abs (z.2-p.2), abs_nonneg (z.2-p.2), sq_nonneg (z.1-p.1)]

private lemma corner_vertex (D : Pt) (C : Charts) (hC : IsChart D C) (a b : ℝ)
    (ha : a ∈ Set.Icc 0 C.TA) (hb : b ∈ Set.Icc 0 C.TB)
    (hdelta : delta D C a b = 0) :
    u D C a = v D C b ∧ u D C a ∈ vertsD D := by
  rcases hC with ⟨_,_,_,_,_,_,_,_,hA,hB,_,_⟩
  have hUa : u D C a ∈ arcA D := by rw [hA]; exact ⟨a,ha,rfl⟩
  have hVb : v D C b ∈ arcB D := by rw [hB]; exact ⟨b,hb,rfl⟩
  have huData : u D C a ∈ SigmaD D ∧ ‖D+u D C a‖ = 1 := by
    unfold arcA at hUa; split_ifs at hUa <;> first | simpa using hUa | exact hUa
  have hvData : v D C b ∈ SigmaD D ∧ dist (D+v D C b) e = 1 := by
    unfold arcB at hVb; split_ifs at hVb <;> first | simpa using hVb | exact hVb
  have hu : ‖u D C a‖ = 1 := huData.1.1
  have hv : ‖v D C b‖ = 1 := hvData.1.1
  have habs : |inner ℝ (u D C a) (v D C b)| ≤ 1 := by
    simpa [hu,hv] using abs_real_inner_le_norm (u D C a) (v D C b)
  have hx : inner ℝ (u D C a) (v D C b) = 1 := by
    have hcos := congrArg Real.cos hdelta
    dsimp [delta] at hcos
    rwa [Real.cos_arccos (abs_le.mp habs).1 (abs_le.mp habs).2, Real.cos_zero] at hcos
  have heq : u D C a = v D C b := by
    have hnorm := norm_sub_sq_real (u D C a) (v D C b)
    rw [hu,hv,hx] at hnorm
    have hz : ‖u D C a - v D C b‖ = 0 := by nlinarith [norm_nonneg (u D C a - v D C b)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  exact ⟨heq, hu, huData.2, by simpa [heq] using hvData.2⟩

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_inverse_sine_rectangle_integrable (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D-e‖ < 1) (hC : IsChart D C)
    (h00 : delta D C 0 0 = 0) (hdd : delta D C C.TA C.TB = 0)
    (hrange : ∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB,
      ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) →
      inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1) :
    IntegrableOn (fun z : ℝ × ℝ => (Real.sin (delta D C z.1 z.2))⁻¹)
      (Set.Icc 0 C.TA ×ˢ Set.Icc 0 C.TB) volume := by
  let K := Set.Icc 0 C.TA ×ˢ Set.Icc 0 C.TB
  let S : (ℝ × ℝ) → ℝ := fun z => Real.sin (delta D C z.1 z.2)
  have hsp : 0 ≤ C.TA ∧ 0 ≤ C.TB := ⟨hC.2.2.2.2.1.le,hC.2.2.2.2.2.1.le⟩
  have hcont : Continuous S := by unfold S delta u v circlePt; fun_prop
  apply SphereGeom.Aux.Santalo.compact_inverse_integrable S K
    (isCompact_Icc.prod isCompact_Icc) hcont
  · intro z hz; dsimp [S,delta]; rw [Real.sin_arccos]; positivity
  · intro p hp hzero
    have hcorner : (p.1=0 ∧ p.2=0) ∨ (p.1=C.TA ∧ p.2=C.TB) := by
      by_contra hh
      have hx := hrange p.1 hp.1 p.2 hp.2 hh
      have hpos : 0 < S p := by
        dsimp [S,delta]; rw [Real.sin_arccos]; exact Real.sqrt_pos.2 (by nlinarith [hx.1,hx.2])
      exact hpos.ne' hzero
    have hd : delta D C p.1 p.2 = 0 := by
      rcases hcorner with h|h
      · simpa [h.1,h.2] using h00
      · simpa [h.1,h.2] using hdd
    obtain ⟨heq,hv⟩ := corner_vertex D C hC p.1 p.2 hp.1 hp.2 hd
    obtain ⟨c,hc,hsin⟩ := chart_local_sine D C hD hoff hR hC p.1 p.2 heq hv
    refine ⟨c,hc,?_⟩
    filter_upwards [hsin] with z hz
    exact (mul_le_mul_of_nonneg_left (norm_le_radius z p) hc.le).trans hz
