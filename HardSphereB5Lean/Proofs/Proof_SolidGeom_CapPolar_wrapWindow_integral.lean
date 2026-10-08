import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_wrapWindow
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SolidGeom.CapPolar
set_option maxHeartbeats 1400000
private lemma WI_window_set (T A B : ℝ) (hT : 0<T) (hA : 0≤A) (hAT : A<T)
    (hAB : A<B) (hBT : B<A+T) : wrapWindow T A B=clippedWindow T A B := by
  ext x
  simp only [wrapWindow,Set.mem_inter_iff,Set.mem_Ioo,Set.mem_setOf_eq]
  have hk01 (hx : 0<x ∧ x<T) (k : ℤ) (hk : A<x+(k:ℝ)*T ∧ x+(k:ℝ)*T<B) :
      k=0 ∨ k=1 := by
    have hk0 : 0≤k := by
      by_contra hn
      have hkn : k≤ -1 := by omega
      have hknr : (k:ℝ)≤ -1 := by exact_mod_cast hkn
      have hh := mul_le_mul_of_nonneg_right hknr hT.le
      nlinarith
    have hk1 : k≤1 := by
      by_contra hn
      have hkn : 2≤k := by omega
      have hknr : (2:ℝ)≤ (k:ℝ) := by exact_mod_cast hkn
      have hh := mul_le_mul_of_nonneg_right hknr hT.le
      nlinarith
    omega
  by_cases hB : B≤T
  · simp only [clippedWindow,if_pos hB,Set.mem_Ioo]
    constructor
    · rintro ⟨hx,k,hk⟩
      rcases hk01 hx k hk with h0|h1
      · simpa only [h0,Int.cast_zero,zero_mul,add_zero] using hk
      · rw [h1] at hk
        norm_num at hk
        nlinarith
    · intro hx
      refine ⟨⟨lt_of_le_of_lt hA hx.1,lt_of_lt_of_le hx.2 hB⟩,0,?_⟩
      simpa only [Int.cast_zero,zero_mul,add_zero] using hx
  · simp only [clippedWindow,if_neg hB,Set.mem_union,Set.mem_Ioo]
    have hTB : T<B := lt_of_not_ge hB
    constructor
    · rintro ⟨hx,k,hk⟩
      rcases hk01 hx k hk with h0|h1
      · rw [h0] at hk
        simp only [Int.cast_zero,zero_mul,add_zero] at hk
        exact Or.inl ⟨hk.1,hx.2⟩
      · rw [h1] at hk
        simp only [Int.cast_one,one_mul] at hk
        exact Or.inr ⟨hx.1,by linarith [hk.2]⟩
    · rintro (hx|hx)
      · refine ⟨⟨lt_of_le_of_lt hA hx.1,hx.2⟩,0,?_⟩
        simpa only [Int.cast_zero,zero_mul,add_zero] using (show A<x ∧ x<B from ⟨hx.1,hx.2.trans hTB⟩)
      · refine ⟨⟨hx.1,by linarith [hx.2]⟩,1,?_⟩
        simp only [Int.cast_one,one_mul]
        constructor <;> linarith [hx.1,hx.2]
private lemma WI_open_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) (a b : ℝ) (hab : a≤b) :
    (∫ x in Set.Ioo a b, f x)=∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_congr_set Ioo_ae_eq_Ioc
theorem proof_SolidGeom_CapPolar_wrapWindow_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : Continuous f)
    (T A B : ℝ) (hT : 0<T) (hA : 0≤A) (hAT : A<T) (hAB : A<B) (hBT : B<A+T)
    (hp : Function.Periodic f T) :
    (∫ x in SolidGeom.CapPolar.wrapWindow T A B, f x)=∫ x in A..B, f x  := by
  rw [WI_window_set T A B hT hA hAT hAB hBT]
  by_cases hB : B≤T
  · rw [clippedWindow,if_pos hB]
    exact WI_open_interval f A B hAB.le
  · have hTB : T<B := lt_of_not_ge hB
    rw [clippedWindow,if_neg hB]
    have hd : Disjoint (Set.Ioo A T) (Set.Ioo 0 (B-T)) := by
      apply Set.disjoint_left.mpr
      rintro x hx hy
      simp only [Set.mem_Ioo] at hx hy
      linarith [hx.1,hy.2]
    rw [setIntegral_union hd measurableSet_Ioo
      (hf.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self)
      (hf.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self),
      WI_open_interval f A T hAT.le,WI_open_interval f 0 (B-T) (by linarith)]
    have hshift : (∫ x in (0)..(B-T), f x)=∫ x in T..B, f x := by
      calc
        _ = ∫ x in (0)..(B-T), f (x+T) := intervalIntegral.integral_congr (fun x _ => (hp x).symm)
        _ = ∫ x in T..B, f x := by
          simpa only [zero_add,sub_add_cancel] using (intervalIntegral.integral_comp_add_right (f:=f) (a:=0) (b:=B-T) T)
    rw [hshift]
    exact intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable A T) (hf.intervalIntegrable T B)
#print axioms proof_SolidGeom_CapPolar_wrapWindow_integral
