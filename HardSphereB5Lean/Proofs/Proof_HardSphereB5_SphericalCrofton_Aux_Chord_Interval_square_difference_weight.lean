import Mathlib
set_option autoImplicit false
open MeasureTheory Real
noncomputable section
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_square_difference_weight (h : ℝ → ENNReal) (hh : Measurable h) (L : ℝ) : (∫⁻ s in Set.Ioc 0 L, ∫⁻ t in Set.Ioc 0 L, h (t - s)) = ∫⁻ r, h r * ENNReal.ofReal (min L (L - r) - max 0 (-r)) := by
  let I : Set ℝ := Set.Ioc 0 L
  have hI : MeasurableSet I := measurableSet_Ioc
  let j : ℝ → ℝ → ENNReal := fun s r => if s ∈ I ∧ r + s ∈ I then h r else 0
  have hj : Measurable (Function.uncurry j) :=
    Measurable.ite ((hI.preimage measurable_fst).inter
      (hI.preimage (measurable_snd.add measurable_fst)))
      (hh.comp measurable_snd) measurable_const
  have he : (∫⁻ s in I, ∫⁻ t in I, h (t - s)) = ∫⁻ s, ∫⁻ r, j s r := by
    rw [← lintegral_indicator hI]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ I
    · rw [Set.indicator_of_mem hs, ← lintegral_indicator hI]
      rw [← lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun t => I.indicator (fun t => h (t - s)) t) s]
      apply lintegral_congr
      intro r
      by_cases hr : r + s ∈ I <;> simp [j, hs, hr, Set.indicator]
    · simp [j, hs, Set.indicator]
  rw [he, lintegral_lintegral_swap hj.aemeasurable]
  apply lintegral_congr
  intro r
  have hset : {s : ℝ | s ∈ I ∧ r + s ∈ I} =
      Set.Ioc (max 0 (-r)) (min L (L - r)) := by
    ext s
    simp only [I, Set.mem_setOf_eq, Set.mem_Ioc, max_lt_iff, le_min_iff]
    constructor
    · intro hs
      exact ⟨⟨hs.1.1, by linarith [hs.2.1]⟩, ⟨hs.1.2, by linarith [hs.2.2]⟩⟩
    · intro hs
      exact ⟨⟨hs.1.1, hs.2.1⟩, ⟨by linarith [hs.1.2], by linarith [hs.2.2]⟩⟩
  have hjr : (fun s => j s r) = (Set.Ioc (max 0 (-r)) (min L (L - r))).indicator (fun _ => h r) := by
    rw [← hset]
    funext s
    simp [j, Set.indicator]
  rw [hjr, lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc]
