import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom
set_option maxHeartbeats 2000000

private lemma sector_cos_bounds (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ π) (htl : -b ≤ t) (htr : t ≤ a) :
    cos (t - 2 * a) ≤ cos t ∧ cos (t + 2 * b) ≤ cos t := by
  have hsa : 0 ≤ sin a := sin_nonneg_of_nonneg_of_le_pi ha (by linarith)
  have hsb : 0 ≤ sin b := sin_nonneg_of_nonneg_of_le_pi hb (by linarith)
  have hsta : sin (t - a) ≤ 0 :=
    sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  have hstb : 0 ≤ sin (t + b) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hida : cos (t - 2 * a) - cos t = 2 * (sin (t - a) * sin a) := by
    calc
      cos (t - 2 * a) - cos t = cos ((t - a) - a) - cos ((t - a) + a) := by
        congr 2 <;> ring
      _ = 2 * (sin (t - a) * sin a) := by rw [cos_sub, cos_add]; ring
  have hidb : cos (t + 2 * b) - cos t = -2 * (sin (t + b) * sin b) := by
    calc
      cos (t + 2 * b) - cos t = cos ((t + b) + b) - cos ((t + b) - b) := by
        congr 2 <;> ring
      _ = -2 * (sin (t + b) * sin b) := by rw [cos_add, cos_sub]; ring
  constructor
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg hsta hsa]
  · nlinarith [mul_nonneg hstb hsb]

private lemma sector_even_integral (F : ℝ → ℝ) (hF : Continuous F) (a b : ℝ) :
    (∫ t in -b..a, F (cos t)) =
      (∫ t in (0 : ℝ)..a, F (cos t)) + ∫ t in (0 : ℝ)..b, F (cos t) := by
  have hc : Continuous (fun t : ℝ => F (cos t)) := hF.comp continuous_cos
  have hneg : (∫ t in -b..(0 : ℝ), F (cos t)) = ∫ t in (0 : ℝ)..b, F (cos t) := by
    calc
      (∫ t in -b..(0 : ℝ), F (cos t)) = ∫ t in -b..(0 : ℝ), F (cos (-t)) := by
        simp only [cos_neg]
      _ = ∫ t in -(0 : ℝ)..-(-b), F (cos t) :=
        intervalIntegral.integral_comp_neg (fun t : ℝ => F (cos t))
      _ = ∫ t in (0 : ℝ)..b, F (cos t) := by simp
  calc
    (∫ t in -b..a, F (cos t)) =
        (∫ t in -b..(0 : ℝ), F (cos t)) + ∫ t in (0 : ℝ)..a, F (cos t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable (-b) 0) (hc.intervalIntegrable 0 a)).symm
    _ = _ := by rw [hneg]; ring

theorem proof_SolidGeom_integral_max_cos_sectors (F : ℝ → ℝ) (hF : Continuous F) (ψ α₀ α₁ α₂ : ℝ) (h0 : 0 < α₀)
    (h1 : 0 < α₁) (h2 : 0 < α₂) (hs : α₀ + α₁ + α₂ = π) :
    ∫ φ in ψ..ψ + 2 * π,
        F (max (cos (φ - ψ)) (max (cos (φ - (ψ + 2 * α₂))) (cos (φ - (ψ + 2 * α₂ + 2 * α₀))))) =
      2 * ((∫ t in (0 : ℝ)..α₀, F (cos t)) + (∫ t in (0 : ℝ)..α₁, F (cos t)) +
        ∫ t in (0 : ℝ)..α₂, F (cos t)) := by
  let g : ℝ → ℝ := fun x =>
    F (max (cos x) (max (cos (x - 2 * α₂)) (cos (x - (2 * α₂ + 2 * α₀)))))
  have hg : Continuous g := by dsimp [g]; fun_prop
  have htrans :
      (∫ φ in ψ..ψ + 2 * π,
        F (max (cos (φ - ψ)) (max (cos (φ - (ψ + 2 * α₂)))
          (cos (φ - (ψ + 2 * α₂ + 2 * α₀)))))) = ∫ x in (0 : ℝ)..2 * π, g x := by
    have H := intervalIntegral.integral_comp_sub_right (a := ψ) (b := ψ + 2 * π) g ψ
    have htop : ψ + 2 * π - ψ = 2 * π := by ring
    rw [sub_self, htop] at H
    rw [← H]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [g]
    rw [show x - (ψ + 2 * α₂) = (x - ψ) - 2 * α₂ by ring,
      show x - (ψ + 2 * α₂ + 2 * α₀) = (x - ψ) - (2 * α₂ + 2 * α₀) by ring]
  have hgper : Function.Periodic g (2 * π) := by
    intro x
    dsimp [g]
    rw [show x + 2 * π - 2 * α₂ = (x - 2 * α₂) + 2 * π by ring,
      show x + 2 * π - (2 * α₂ + 2 * α₀) = (x - (2 * α₂ + 2 * α₀)) + 2 * π by ring]
    simp only [cos_add_two_pi]
  have hshift : (∫ x in (0 : ℝ)..2 * π, g x) = ∫ x in -α₁..2 * π - α₁, g x := by
    simpa only [zero_add, show -α₁ + 2 * π = 2 * π - α₁ by ring] using
      hgper.intervalIntegral_add_eq 0 (-α₁)
  have cell0 : (∫ x in -α₁..α₂, g x) =
      (∫ t in (0 : ℝ)..α₂, F (cos t)) + ∫ t in (0 : ℝ)..α₁, F (cos t) := by
    calc
      (∫ x in -α₁..α₂, g x) = ∫ x in -α₁..α₂, F (cos x) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le (by linarith : -α₁ ≤ α₂)]
        intro x hx
        have hb := sector_cos_bounds α₂ α₁ x h2.le h1.le (by linarith) hx.1 hx.2
        have hperiod : cos (x - (2 * α₂ + 2 * α₀)) = cos (x + 2 * α₁) := by
          rw [show x - (2 * α₂ + 2 * α₀) = (x + 2 * α₁) - 2 * π by linarith,
            cos_sub_two_pi]
        dsimp [g]
        rw [hperiod, max_eq_left (max_le hb.1 hb.2)]
      _ = _ := sector_even_integral F hF α₂ α₁
  have cell1 : (∫ x in α₂..2 * α₂ + α₀, g x) =
      (∫ t in (0 : ℝ)..α₀, F (cos t)) + ∫ t in (0 : ℝ)..α₂, F (cos t) := by
    calc
      (∫ x in α₂..2 * α₂ + α₀, g x) =
          ∫ x in α₂..2 * α₂ + α₀, F (cos (x - 2 * α₂)) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le (by linarith : α₂ ≤ 2 * α₂ + α₀)]
        intro x hx
        have hb := sector_cos_bounds α₀ α₂ (x - 2 * α₂) h0.le h2.le
          (by linarith) (by linarith [hx.1]) (by linarith [hx.2])
        have hprev : cos x ≤ cos (x - 2 * α₂) := by
          convert hb.2 using 1 <;> congr 1 <;> ring
        have hnext : cos (x - (2 * α₂ + 2 * α₀)) ≤ cos (x - 2 * α₂) := by
          convert hb.1 using 1 <;> congr 1 <;> ring
        dsimp [g]
        rw [max_eq_left hnext, max_eq_right hprev]
      _ = ∫ t in -α₂..α₀, F (cos t) := by
        rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => F (cos t)) (2 * α₂)]
        congr 1 <;> ring
      _ = _ := sector_even_integral F hF α₀ α₂
  have cell2 : (∫ x in (2 * α₂ + α₀)..2 * π - α₁, g x) =
      (∫ t in (0 : ℝ)..α₁, F (cos t)) + ∫ t in (0 : ℝ)..α₀, F (cos t) := by
    calc
      (∫ x in (2 * α₂ + α₀)..2 * π - α₁, g x) =
          ∫ x in (2 * α₂ + α₀)..2 * π - α₁, F (cos (x - (2 * α₂ + 2 * α₀))) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le (by linarith : 2 * α₂ + α₀ ≤ 2 * π - α₁)]
        intro x hx
        have hb := sector_cos_bounds α₁ α₀ (x - (2 * α₂ + 2 * α₀)) h1.le h0.le
          (by linarith) (by linarith [hx.1]) (by linarith [hx.2])
        have hnext : cos x ≤ cos (x - (2 * α₂ + 2 * α₀)) := by
          calc
            cos x = cos ((x - (2 * α₂ + 2 * α₀)) - 2 * α₁) := by
              rw [show (x - (2 * α₂ + 2 * α₀)) - 2 * α₁ = x - 2 * π by linarith,
                cos_sub_two_pi]
            _ ≤ _ := hb.1
        have hprev : cos (x - 2 * α₂) ≤ cos (x - (2 * α₂ + 2 * α₀)) := by
          convert hb.2 using 1 <;> congr 1 <;> ring
        dsimp [g]
        rw [max_eq_right hprev, max_eq_right hnext]
      _ = ∫ t in -α₀..α₁, F (cos t) := by
        rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => F (cos t))
          (2 * α₂ + 2 * α₀)]
        have hl : (2 * α₂ + α₀) - (2 * α₂ + 2 * α₀) = -α₀ := by ring
        have hr : (2 * π - α₁) - (2 * α₂ + 2 * α₀) = α₁ := by linarith
        rw [hl, hr]
      _ = _ := sector_even_integral F hF α₁ α₀
  have hsum :
      ((∫ x in -α₁..α₂, g x) + (∫ x in α₂..2 * α₂ + α₀, g x)) +
        (∫ x in (2 * α₂ + α₀)..2 * π - α₁, g x) =
      ∫ x in -α₁..2 * π - α₁, g x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (-α₁) α₂) (hg.intervalIntegrable α₂ (2 * α₂ + α₀))]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (-α₁) (2 * α₂ + α₀))
      (hg.intervalIntegrable (2 * α₂ + α₀) (2 * π - α₁))
  rw [htrans, hshift, ← hsum, cell0, cell1, cell2]
  ring
