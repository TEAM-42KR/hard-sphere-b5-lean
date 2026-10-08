import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
set_option autoImplicit false
open MeasureTheory SphereGeom
theorem proof_CircleArc_intervalIntersection (c : E3) (e : Fin 2 → E3) (he : Orthonormal ℝ e)
    (r : ℝ) (hr : 0 < r) (a b d f : ℝ)
    (hspan : max b f - min a d < 2 * Real.pi) :
    (circlePt c (e 0) (e 1) r '' Set.Icc a b) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc d f) =
      circlePt c (e 0) (e 1) r '' Set.Icc (max a d) (min b f) ∧
    arcMeasure ((circlePt c (e 0) (e 1) r '' Set.Icc a b) ∩
        (circlePt c (e 0) (e 1) r '' Set.Icc d f)) =
      ENNReal.ofReal (r * (min b f - max a d)) := by
  have hinj : Set.InjOn (circlePt c (e 0) (e 1) r)
      (Set.Icc (min a d) (max b f)) := by
    intro x hx y hy hxy
    have h0 := congrArg (fun p : E3 => inner ℝ (e 0) p) hxy
    have h1 := congrArg (fun p : E3 => inner ℝ (e 1) p) hxy
    have he00 : inner ℝ (e 0) (e 0) = 1 := by simpa using (orthonormal_iff_ite.mp he) 0 0
    have he01 : inner ℝ (e 0) (e 1) = 0 := by simpa using (orthonormal_iff_ite.mp he) 0 1
    have he10 : inner ℝ (e 1) (e 0) = 0 := by simpa using (orthonormal_iff_ite.mp he) 1 0
    have he11 : inner ℝ (e 1) (e 1) = 1 := by simpa using (orthonormal_iff_ite.mp he) 1 1
    simp only [circlePt, inner_add_right, inner_smul_right, he00, he01, he10, he11,
      mul_one, mul_zero, add_zero, zero_add] at h0 h1
    have hc : Real.cos x = Real.cos y := mul_left_cancel₀ (ne_of_gt hr) (add_left_cancel h0)
    have hs : Real.sin x = Real.sin y := mul_left_cancel₀ (ne_of_gt hr) (add_left_cancel h1)
    have hcos : Real.cos (x - y) = 1 := by
      rw [Real.cos_sub, hc, hs]
      nlinarith [Real.sin_sq_add_cos_sq y]
    have hdiff : x - y = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hx.1, hy.2])
        (by linarith [hx.2, hy.1])).mp hcos
    linarith
  have hsets : (circlePt c (e 0) (e 1) r '' Set.Icc a b) ∩
      (circlePt c (e 0) (e 1) r '' Set.Icc d f) =
      circlePt c (e 0) (e 1) r '' Set.Icc (max a d) (min b f) := by
    have hmap := Set.image_inter_on (f := circlePt c (e 0) (e 1) r)
      (s := Set.Icc a b) (t := Set.Icc d f) (by
        intro x hx y hy heq
        apply hinj _ _ heq
        · exact ⟨le_trans (min_le_right _ _) hx.1,
            le_trans hx.2 (le_max_right _ _)⟩
        · exact ⟨le_trans (min_le_left _ _) hy.1,
            le_trans hy.2 (le_max_left _ _)⟩)
    rw [Set.Icc_inter_Icc] at hmap
    exact hmap.symm
  refine ⟨hsets, ?_⟩
  rw [hsets]
  by_cases hnonempty : max a d ≤ min b f
  · exact SphereGeom.arcMeasure_circle_arc c e he r hr _ _ hnonempty
      (by
        have hlow : min a d ≤ max a d := le_trans (min_le_left _ _) (le_max_left _ _)
        have hup : min b f ≤ max b f := le_trans (min_le_left _ _) (le_max_left _ _)
        linarith)
  · have hempty : Set.Icc (max a d) (min b f) = ∅ := Set.Icc_eq_empty_of_lt (lt_of_not_ge hnonempty)
    rw [hempty, Set.image_empty, measure_empty]
    symm
    apply ENNReal.ofReal_of_nonpos
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) (by linarith)
