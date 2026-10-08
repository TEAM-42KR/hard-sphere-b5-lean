import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_measurable_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Pair_arcMeasure_greatCircle_frame
set_option autoImplicit false
noncomputable section
open MeasureTheory SphereGeom Real
open scoped Classical
set_option maxHeartbeats 1200000

private theorem finite_unitCircle_line (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    Set.Finite {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 = 1 ∧ a * z.1 + b * z.2 = 0} := by
  classical
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    refine (Set.toFinite ({(1, 0), (-1, 0)} : Set (ℝ × ℝ))).subset ?_
    rintro ⟨x,y⟩ ⟨hn, hl⟩
    have hy : y = 0 := by simpa [ha, hb] using hl
    have hx : x ^ 2 = (1 : ℝ) ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx with hx | hx
    · simp [hx, hy]
    · simp [hx, hy]
  · let P : Polynomial ℝ := Polynomial.C (a ^ 2 + b ^ 2) * Polynomial.X ^ 2 - Polynomial.C (a ^ 2)
    have hP : P ≠ 0 := by
      intro h
      have hv := congrArg (Polynomial.eval (0 : ℝ)) h
      have hsq : a ^ 2 = 0 := by simpa [P] using hv
      exact ha (sq_eq_zero_iff.mp hsq)
    apply Set.Finite.of_finite_image (f := fun z : ℝ × ℝ => z.2)
    · refine (Polynomial.finite_setOf_isRoot hP).subset ?_
      rintro y ⟨⟨x,y⟩, ⟨hn,hl⟩, rfl⟩
      change P.eval y = 0
      simp only [P, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      have hs : (a * x) ^ 2 = (b * y) ^ 2 := by
        have hh : a * x = -(b * y) := by linarith
        rw [hh]
        ring
      have ht := congrArg (fun q : ℝ => a ^ 2 * q) hn
      nlinarith [hs, ht]
    · rintro ⟨x,y⟩ ⟨hn,hl⟩ ⟨x',y'⟩ ⟨hn',hl'⟩ hyy
      change y = y' at hyy
      have hxx : x = x' := by
        apply (mul_left_cancel₀ ha)
        simp only [Prod.fst, Prod.snd] at hl hl'
        rw [hyy] at hl
        linarith
      exact Prod.ext hxx hyy

theorem proof_SphereGeom_Aux_Chord_arcMeasure_greatCircle_closedHemisphere (n p : E3) (hn : ‖n‖ = 1) (hp : ‖p‖ = 1)
    (hpn : p ≠ n) (hpnm : p ≠ -n) :
    arcMeasure (greatCircle p ∩ {u : E3 | 0 ≤ inner ℝ n u}) = ENNReal.ofReal Real.pi := by
  obtain ⟨F₁,F₂,hF₁,hF₂,hF⟩ := SphereGeom.exists_measurable_frame
  let v₁ := F₁ p
  let v₂ := F₂ p
  have hv : Orthonormal ℝ ![v₁,v₂,p] := hF p hp
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range ![v₁,v₂,p]) := by
    apply Eq.ge
    apply hv.linearIndependent.span_eq_top_of_card_eq_finrank
    simp [E3]
  let B : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk hv hspan
  have hb0 : B 0 = v₁ := by simp [B]
  have hb1 : B 1 = v₂ := by simp [B]
  have hb2 : B 2 = p := by simp [B]
  have hsum (u : E3) : B.repr u 0 • v₁ + B.repr u 1 • v₂ + B.repr u 2 • p = u := by
    simpa [Fin.sum_univ_succ, hb0, hb1, hb2, add_assoc] using B.sum_repr u
  have hnorm (u : E3) (hu : ‖u‖ = 1) :
      B.repr u 0 ^ 2 + B.repr u 1 ^ 2 + B.repr u 2 ^ 2 = 1 := by
    have hh : ‖B.repr u‖ ^ 2 = 1 := by rw [B.repr.norm_map, hu]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq] at hh
    simpa [Fin.sum_univ_succ, add_assoc] using hh
  have hinner (u : E3) : inner ℝ n u =
      B.repr n 0 * B.repr u 0 + B.repr n 1 * B.repr u 1 + B.repr n 2 * B.repr u 2 := by
    have hh := B.repr.inner_map_map n u
    rw [PiLp.inner_apply, Fin.sum_univ_three] at hh
    simpa only [Real.inner_apply] using hh.symm
  have hnot : B.repr n 0 ≠ 0 ∨ B.repr n 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have hs : B.repr n 2 ^ 2 = (1 : ℝ) ^ 2 := by nlinarith [hnorm n hn]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hc | hc
    · have hnp : n = p := by simpa [h.1,h.2,hc] using (hsum n).symm
      exact hpn hnp.symm
    · have hnp : n = -p := by simpa [h.1,h.2,hc] using (hsum n).symm
      apply hpnm
      rw [hnp, neg_neg]
  let Z : Set E3 := greatCircle p ∩ {u : E3 | inner ℝ n u = 0}
  have hzcoord {u : E3} (hu : u ∈ Z) :
      B.repr u 2 = 0 ∧ B.repr u 0 ^ 2 + B.repr u 1 ^ 2 = 1 ∧
        B.repr n 0 * B.repr u 0 + B.repr n 1 * B.repr u 1 = 0 := by
    have hpu : B.repr u 2 = 0 := by
      simpa [B.repr_apply_apply, hb2] using hu.1.2
    refine ⟨hpu, ?_, ?_⟩
    · nlinarith [hnorm u hu.1.1]
    · have hh := hinner u
      rw [hu.2,hpu] at hh
      nlinarith
  have hzfin : Z.Finite := by
    apply Set.Finite.of_finite_image (f := fun u : E3 => (B.repr u 0, B.repr u 1))
    · refine (finite_unitCircle_line (B.repr n 0) (B.repr n 1) hnot).subset ?_
      rintro z ⟨u,hu,rfl⟩
      exact (hzcoord hu).2
    · intro u hu v hv huv
      apply B.repr.injective
      apply PiLp.ext
      intro i
      fin_cases i
      · exact congrArg Prod.fst huv
      · exact congrArg Prod.snd huv
      · exact (hzcoord hu).1.trans (hzcoord hv).1.symm
  letI : NullSingletonClass arcMeasure := by
    unfold arcMeasure
    exact Measure.nullSingletonClass_hausdorff E3 (by norm_num : (0 : ℝ) < 1)
  have hz : arcMeasure Z = 0 := hzfin.measure_zero arcMeasure
  let A : Set E3 := greatCircle p ∩ {u : E3 | 0 ≤ inner ℝ n u}
  let C : Set E3 := greatCircle p ∩ {u : E3 | inner ℝ n u ≤ 0}
  have hC : MeasurableSet C := by
    exact ((isClosed_eq continuous_norm continuous_const).measurableSet.inter
      (isClosed_eq (by fun_prop : Continuous (fun u : E3 => inner ℝ p u)) continuous_const).measurableSet).inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hUnion : A ∪ C = greatCircle p := by
    ext u
    simp only [A,C,Set.mem_union,Set.mem_inter_iff,Set.mem_setOf_eq]
    constructor
    · rintro (h|h) <;> exact h.1
    · intro h
      rcases le_total (0 : ℝ) (inner ℝ n u) with hu | hu
      · exact Or.inl ⟨h,hu⟩
      · exact Or.inr ⟨h,hu⟩
  have hInter : A ∩ C = Z := by
    ext u
    simp only [A,C,Z,Set.mem_inter_iff,Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h,ha⟩,hc,hb⟩
      exact ⟨h,le_antisymm hb ha⟩
    · rintro ⟨h,hz⟩
      exact ⟨⟨h,by simp [hz]⟩,h,by simp [hz]⟩
  have hImage : (fun u : E3 => -u) '' A = C := by
    ext u
    constructor
    · rintro ⟨v,⟨⟨hv,hpv⟩,hnv⟩,rfl⟩
      exact ⟨⟨by simpa using hv,by simp [inner_neg_right,hpv]⟩,by simpa [inner_neg_right] using hnv⟩
    · rintro ⟨⟨hu,hpu⟩,hnu⟩
      refine ⟨-u,⟨⟨by simpa using hu,by simp [inner_neg_right,hpu]⟩,?_⟩,by simp⟩
      simpa [inner_neg_right] using hnu
  have hEq : arcMeasure C = arcMeasure A := by
    rw [← hImage]
    exact (LinearIsometryEquiv.neg ℝ : E3 ≃ₗᵢ[ℝ] E3).isometry.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)) A
  have hGc : arcMeasure (greatCircle p) = ENNReal.ofReal (2 * Real.pi) := by
    have hc : Measurable (circlePt 0 v₁ v₂ 1) := by unfold circlePt; fun_prop
    have hh := congrArg (fun μ : Measure E3 => μ Set.univ)
      (SphereGeom.Aux.Pair.arcMeasure_greatCircle_frame v₁ v₂ p hv)
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Measure.map_apply hc MeasurableSet.univ] at hh
    simpa only [Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Icc, sub_neg_eq_add, ← two_mul] using hh
  have hAdd := measure_union_add_inter (μ := arcMeasure) A hC
  rw [hUnion,hInter,hz,hEq,hGc,add_zero] at hAdd
  have hfinite : arcMeasure A ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    rw [← hGc]
    exact measure_mono Set.inter_subset_left
  apply (ENNReal.toReal_eq_toReal_iff' hfinite ENNReal.ofReal_ne_top).mp
  have ht := congrArg ENNReal.toReal hAdd
  rw [ENNReal.toReal_add hfinite hfinite, ENNReal.toReal_ofReal (by positivity)] at ht
  rw [ENNReal.toReal_ofReal Real.pi_pos.le]
  linarith
