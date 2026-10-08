import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_wrapWindow_integral
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SolidGeom.CapPolar
set_option maxHeartbeats 1000000
private lemma WA_shift (T A B : ℝ) (k : ℤ) :
    wrapWindow T A B=wrapWindow T (A-(k:ℝ)*T) (B-(k:ℝ)*T) := by
  ext x
  simp only [wrapWindow,Set.mem_inter_iff,Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx,m,hl,hr⟩
    refine ⟨hx,m-k,?_,?_⟩ <;> simp only [Int.cast_sub] <;> nlinarith
  · rintro ⟨hx,m,hl,hr⟩
    refine ⟨hx,m+k,?_,?_⟩ <;> simp only [Int.cast_add] <;> nlinarith
theorem proof_SolidGeom_CapPolar_wrapWindow_integral_any {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : Continuous f)
    (T A B : ℝ) (hT : 0<T) (hAB : A<B) (hBT : B<A+T) (hp : Function.Periodic f T) :
    (∫ x in SolidGeom.CapPolar.wrapWindow T A B, f x)=∫ x in A..B, f x  := by
  let k : ℤ := ⌊A/T⌋
  have hfloor : (k:ℝ)≤A/T := Int.floor_le (A/T)
  have hfloor' : A/T<(k:ℝ)+1 := Int.lt_floor_add_one (A/T)
  have hdiv : A/T*T=A := div_mul_cancel₀ A hT.ne'
  have h0 : 0≤A-(k:ℝ)*T := by
    have h := mul_le_mul_of_nonneg_right hfloor hT.le
    rw [hdiv] at h
    linarith
  have h1 : A-(k:ℝ)*T<T := by
    have h := mul_lt_mul_of_pos_right hfloor' hT
    rw [hdiv] at h
    nlinarith
  rw [WA_shift T A B k,wrapWindow_integral f hf T (A-(k:ℝ)*T) (B-(k:ℝ)*T)
    hT h0 h1 (by linarith) (by linarith) hp]
  calc
    _ = ∫ x in (A-(k:ℝ)*T)..(B-(k:ℝ)*T), f (x+(k:ℝ)*T) :=
      intervalIntegral.integral_congr (fun x _ => ((hp.int_mul k) x).symm)
    _ = ∫ x in A..B, f x := by
      simpa only [sub_add_cancel] using
        (intervalIntegral.integral_comp_add_right (f:=f) (a:=A-(k:ℝ)*T) (b:=B-(k:ℝ)*T) ((k:ℝ)*T))
#print axioms proof_SolidGeom_CapPolar_wrapWindow_integral_any
