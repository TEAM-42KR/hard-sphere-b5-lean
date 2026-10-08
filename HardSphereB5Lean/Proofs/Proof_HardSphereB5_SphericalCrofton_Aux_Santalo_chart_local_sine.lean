import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_chart_local_distance
set_option autoImplicit false
noncomputable section
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo Filter
open HardSphereB5.Lean (Pt e)
open scoped Topology

private lemma sin_angle_half_chord (p q : Pt) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hx : 0 ≤ inner ℝ p q) : ‖p - q‖ / 2 ≤ Real.sin (Real.arccos (inner ℝ p q)) := by
  have hupper : inner ℝ p q ≤ 1 := by
    calc
      _ ≤ |inner ℝ p q| := le_abs_self _
      _ ≤ ‖p‖ * ‖q‖ := abs_real_inner_le_norm p q
      _ = 1 := by rw [hp, hq]; norm_num
  rw [Real.sin_arccos]
  have hs := Real.sq_sqrt (show 0 ≤ 1 - inner ℝ p q ^ 2 by nlinarith [hx, hupper])
  have hn := norm_sub_sq_real p q
  rw [hp, hq] at hn
  nlinarith [Real.sqrt_nonneg (1 - inner ℝ p q ^ 2), norm_nonneg (p - q), mul_nonneg hx (sub_nonneg.mpr hupper)]

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_chart_local_sine (D : Pt) (C : Charts) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) (hC : IsChart D C) (a b : ℝ)
    (heq : u D C a = v D C b) (hv : u D C a ∈ vertsD D) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : ℝ × ℝ in
      𝓝[Set.Icc 0 C.TA ×ˢ Set.Icc 0 C.TB] (a, b),
      c * Real.sqrt ((z.1 - a) ^ 2 + (z.2 - b) ^ 2) ≤
        Real.sin (delta D C z.1 z.2) := by
  obtain ⟨c, hc, hdist⟩ := chart_local_distance D C hD hoff hR hC a b heq hv
  have hcont : Continuous (fun z : ℝ × ℝ => inner ℝ (u D C z.1) (v D C z.2)) := by
    unfold u v circlePt; fun_prop
  have h0 : (0 : ℝ) < inner ℝ (u D C a) (v D C b) := by
    rw [← heq, real_inner_self_eq_norm_sq, hv.1]; norm_num
  have hpos : ∀ᶠ z : ℝ × ℝ in 𝓝 (a, b), 0 < inner ℝ (u D C z.1) (v D C z.2) :=
    hcont.continuousAt.eventually (lt_mem_nhds h0)
  rcases hC with ⟨_, _, _, _, _, _, _, _, hA, hB, _, _⟩
  refine ⟨c / 4, by positivity, ?_⟩
  filter_upwards [hdist.filter_mono nhdsWithin_le_nhds,
    hpos.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hx hrect
  have hut : u D C z.1 ∈ arcA D := by rw [hA]; exact ⟨z.1, hrect.1, rfl⟩
  have hvs : v D C z.2 ∈ arcB D := by rw [hB]; exact ⟨z.2, hrect.2, rfl⟩
  have hu : ‖u D C z.1‖ = 1 := by
    unfold arcA at hut; split_ifs at hut <;> first | simpa using hut | exact hut.1.1
  have hv : ‖v D C z.2‖ = 1 := by
    unfold arcB at hvs; split_ifs at hvs <;> first | simpa using hvs | exact hvs.1.1
  have hsin := sin_angle_half_chord _ _ hu hv hx.le
  have hfst : |z.1 - a| ≤ ‖z - (a, b)‖ := by simpa using norm_fst_le (z - (a, b))
  have hsnd : |z.2 - b| ≤ ‖z - (a, b)‖ := by simpa using norm_snd_le (z - (a, b))
  have hrho : Real.sqrt ((z.1 - a) ^ 2 + (z.2 - b) ^ 2) ≤ 2 * ‖z - (a, b)‖ := by
    have hs := Real.sq_sqrt (show 0 ≤ (z.1 - a) ^ 2 + (z.2 - b) ^ 2 by positivity)
    nlinarith [sq_abs (z.1 - a), sq_abs (z.2 - b), norm_nonneg (z - (a, b)),
      abs_nonneg (z.1 - a), abs_nonneg (z.2 - b), Real.sqrt_nonneg ((z.1 - a) ^ 2 + (z.2 - b) ^ 2)]
  dsimp [delta] at *
  nlinarith [mul_le_mul_of_nonneg_left hrho hc.le]
