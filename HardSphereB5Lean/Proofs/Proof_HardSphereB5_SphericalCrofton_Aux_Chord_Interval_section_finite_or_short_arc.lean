import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_finite_or_connected
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_periodic_compact_connected_arc
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_circle_image
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_ArcLength_injOn_Icc
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_circle_arc
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 800000
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_finite_or_short_arc {K : Set Pt} (hK : IsRegularRegionCrofton K) (E1 E2 p : Pt)
    (hE : Orthonormal ℝ ![E1, E2, p]) (hL : chordLen K (greatCircle p) ≤ π) :
    (greatCircle p ∩ K).Finite ∨
      ∃ a b : ℝ, a ≤ b ∧ b - a ≤ π ∧
        greatCircle p ∩ K = circlePt 0 E1 E2 1 '' Set.Icc a b := by
  rcases HardSphereB5.SphericalCrofton.Aux.Chord.Interval.section_finite_or_connected hK p with hf | hc
  · exact Or.inl hf
  right
  let C : ℝ → Pt := circlePt 0 E1 E2 1
  let S : Set Pt := greatCircle p ∩ K
  have h00 : inner ℝ E1 E1 = 1 := by simpa using (orthonormal_iff_ite.mp hE (0 : Fin 3) 0)
  have h01 : inner ℝ E1 E2 = 0 := by simpa using (orthonormal_iff_ite.mp hE (0 : Fin 3) 1)
  have h10 : inner ℝ E2 E1 = 0 := by simpa using (orthonormal_iff_ite.mp hE (1 : Fin 3) 0)
  have h11 : inner ℝ E2 E2 = 1 := by simpa using (orthonormal_iff_ite.mp hE (1 : Fin 3) 1)
  have hp0 : inner ℝ p E1 = 0 := by simpa using (orthonormal_iff_ite.mp hE (2 : Fin 3) 0)
  have hp1 : inner ℝ p E2 = 0 := by simpa using (orthonormal_iff_ite.mp hE (2 : Fin 3) 1)
  have he2 : Orthonormal ℝ ![E1,E2] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  have hinner (s t : ℝ) : inner ℝ (C s) (C t) = Real.cos (s - t) := by
    simp only [C, circlePt, zero_add, one_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, h00, h01, h10, h11,
      mul_one, mul_zero, zero_mul, add_zero, zero_add]
    rw [Real.cos_sub]
    ring
  have hCg (t : ℝ) : C t ∈ greatCircle p := by
    refine ⟨?_, ?_⟩
    · have hh : ‖C t‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, hinner]
        simp
      nlinarith [norm_nonneg (C t)]
    · simp [C, circlePt, inner_add_right, real_inner_smul_right, hp0, hp1]
  have hrange : Set.range C = greatCircle p := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, rfl⟩
      exact hCg t
    · rw [← SphereGeom.Aux.Pair.circle_image E1 E2 p hE]
      exact Set.image_subset_range _ _
  have hgclosed : IsClosed (greatCircle p) :=
    (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have hcomp : IsCompact S := hK.isCompact.inter_left hgclosed
  have hmass : arcMeasure (greatCircle p) = ENNReal.ofReal (2 * π) := by
    rw [← SphereGeom.Aux.Pair.circle_image E1 E2 p hE]
    have hm := SphereGeom.arcMeasure_circle_arc 0 ![E1,E2] he2 1 (by norm_num)
      (-π) π (by linarith [Real.pi_pos]) (by linarith)
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      show π - -π = 2 * π by ring] using hm
  have hnot : ¬ Set.range C ⊆ S := by
    intro hs
    have heq : S = greatCircle p := Set.Subset.antisymm (Set.inter_subset_left) (hrange ▸ hs)
    have hlen : chordLen K (greatCircle p) = 2 * π := by
      change (arcMeasure S).toReal = _
      rw [heq, hmass, ENNReal.toReal_ofReal (by positivity)]
    linarith [Real.pi_pos]
  obtain ⟨x, hx, hxS⟩ := Set.not_subset.mp hnot
  obtain ⟨cut, rfl⟩ := hx
  have hCcont : Continuous C := by unfold C circlePt; fun_prop
  have hper : Function.Periodic C (2 * π) := by
    intro t
    simp [C, circlePt, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hshort : ∀ a b : ℝ, b - a < 2 * π → Set.InjOn C (Set.Icc a b) := by
    intro a b hab
    exact SphereGeom.Aux.ArcLength.injOn_Icc 0 ![E1,E2] he2 1 (by norm_num) a b hab
  have hsub : S ⊆ Set.range C := hrange.symm ▸ Set.inter_subset_left
  obtain ⟨a,b,hab,hb,hgeom⟩ :=
    HardSphereB5.SphericalCrofton.Aux.Chord.Interval.periodic_compact_connected_arc C hCcont
      (2 * π) (by positivity) hper hshort S hc hcomp hsub cut hxS
  have hlen : chordLen K (greatCircle p) = b - a := by
    change (arcMeasure S).toReal = _
    rw [hgeom]
    have hm := SphereGeom.arcMeasure_circle_arc 0 ![E1,E2] he2 1 (by norm_num) a b hab hb.le
    simpa [C, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using congrArg ENNReal.toReal hm
  exact ⟨a,b,hab,hlen ▸ hL,hgeom⟩
