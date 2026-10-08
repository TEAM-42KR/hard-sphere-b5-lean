import HardSphereB5Lean.Theorems.Thm_SolidGeom_sphere_upper_patch_transport
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open scoped Classical
noncomputable section

theorem proof_SolidGeom_ballInter_patch_graph_flux (n : ℕ) (c : Fin n → E3)
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) (a b : ℝ) :
    let K : Set E3 := ⋂ j : Fin n, Metric.closedBall (c j) 1
    let D : Fin n → Set (ℝ × ℝ) := fun i =>
      {p | (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
    let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
      Real.sqrt (1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
      Real.sqrt (1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
    let X : ℝ × ℝ → ℝ → E3 := fun p z => p.1 • e 0 + p.2 • e 1 + z • e 2
    (∑ i : Fin n, ∫ x in K, (a + b * inner ℝ (e 2) x) *
      inner ℝ (e 2) (x - c i) ∂sphereMeasure (c i)) =
    (∑ i : Fin n, ∫ p in D i, if X p (u i p) ∈ K then a + b * u i p else 0) -
    (∑ i : Fin n, ∫ p in D i, if X p (l i p) ∈ K then a + b * l i p else 0) := by
  classical
  dsimp only
  let K : Set E3 := ⋂ j : Fin n, Metric.closedBall (c j) 1
  let D : Fin n → Set (ℝ × ℝ) := fun i =>
    {p | (p.1 - inner ℝ (e 0) (c i)) ^ 2 + (p.2 - inner ℝ (e 1) (c i)) ^ 2 < 1}
  let l : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) -
    Real.sqrt (1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
  let u : Fin n → ℝ × ℝ → ℝ := fun i p => inner ℝ (e 2) (c i) +
    Real.sqrt (1 - (p.1 - inner ℝ (e 0) (c i)) ^ 2 - (p.2 - inner ℝ (e 1) (c i)) ^ 2)
  let X : ℝ × ℝ → ℝ → E3 := fun p z => p.1 • e 0 + p.2 • e 1 + z • e 2
  change (∑ i : Fin n, ∫ x in K, (a + b * inner ℝ (e 2) x) *
      inner ℝ (e 2) (x - c i) ∂sphereMeasure (c i)) =
    (∑ i : Fin n, ∫ p in D i, if X p (u i p) ∈ K then a + b * u i p else 0) -
    (∑ i : Fin n, ∫ p in D i, if X p (l i p) ∈ K then a + b * l i p else 0)
  have hK : MeasurableSet K := MeasurableSet.iInter (fun j => Metric.isClosed_closedBall.measurableSet)
  let q : Fin 3 → E3 := fun k => if k = 2 then -e k else e k
  have hq : Orthonormal ℝ q := by
    rw [orthonormal_iff_ite]
    intro k m
    fin_cases k <;> fin_cases m <;>
      simp [q, inner_neg_left, inner_neg_right, orthonormal_iff_ite.mp he, he.norm_eq_one]
  have hq0 : q 0 = e 0 := by simp [q]
  have hq1 : q 1 = e 1 := by simp [q]
  have hq2 : q 2 = -e 2 := by simp [q]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  let t := c i
  let P : E3 → ℝ × ℝ := fun x => (inner ℝ (e 0) x, inner ℝ (e 1) x)
  let Hp : Set E3 := {x | 0 < inner ℝ (e 2) (x - t)}
  let Hm : Set E3 := {x | 0 < -inner ℝ (e 2) (x - t)}
  let f : E3 → ℝ := fun x => (a + b * inner ℝ (e 2) x) * inner ℝ (e 2) (x - t)
  change (∫ x in K, f x ∂sphereMeasure t) =
    (∫ p in D i, if X p (u i p) ∈ K then a + b * u i p else 0) -
    (∫ p in D i, if X p (l i p) ∈ K then a + b * l i p else 0)
  let basis : OrthonormalBasis (Fin 3) ℝ E3 :=
    (basisOfOrthonormalOfCardEqFinrank he (by simp [E3])).toOrthonormalBasis (by simpa using he)
  have hb (j : Fin 3) : basis j = e j := by simp [basis]
  have hrad (x : E3) (hs : x ∈ Metric.sphere t 1) :
      1 - ((P x).1 - inner ℝ (e 0) t) ^ 2 - ((P x).2 - inner ℝ (e 1) t) ^ 2 =
        (inner ℝ (e 2) (x - t)) ^ 2 := by
    have hnorm : ‖x - t‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hs
    have hsum : ((P x).1 - inner ℝ (e 0) t) ^ 2 + ((P x).2 - inner ℝ (e 1) t) ^ 2 +
        (inner ℝ (e 2) (x - t)) ^ 2 = 1 := by
      simpa [P, Fin.sum_univ_three, hb, inner_sub_right, hnorm] using basis.sum_sq_inner_right (x - t)
    linarith
  have hucoord (x : E3) (hs : x ∈ Metric.sphere t 1) (hp : x ∈ Hp) :
      u i (P x) = inner ℝ (e 2) x := by
    change inner ℝ (e 2) t + Real.sqrt
      (1 - ((P x).1 - inner ℝ (e 0) t)^2 - ((P x).2 - inner ℝ (e 1) t)^2) = _
    rw [hrad x hs, Real.sqrt_sq (le_of_lt hp)]
    simp [inner_sub_right]
  have hlcoord (x : E3) (hs : x ∈ Metric.sphere t 1) (hm : x ∈ Hm) :
      l i (P x) = inner ℝ (e 2) x := by
    change inner ℝ (e 2) t - Real.sqrt
      (1 - ((P x).1 - inner ℝ (e 0) t)^2 - ((P x).2 - inner ℝ (e 1) t)^2) = _
    rw [hrad x hs, Real.sqrt_sq_eq_abs, abs_of_neg (neg_pos.mp hm)]
    simp [inner_sub_right]
  have hHp : MeasurableSet Hp := (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hHm : MeasurableSet Hm := (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hsc : ∀ᵐ x ∂sphereMeasure t, x ∈ Metric.sphere t 1 := by
    rw [sphereMeasure]
    have ht : Measurable (fun v : Metric.sphere (0 : E3) 1 => t + (v : E3)) := by fun_prop
    apply (ae_map_iff ht.aemeasurable Metric.isClosed_sphere.measurableSet).2
    filter_upwards [] with v
    simpa [Metric.mem_sphere, dist_eq_norm] using v.property
  have hsP : ∀ᵐ x ∂(sphereMeasure t).restrict (K ∩ Hp), x ∈ Metric.sphere t 1 :=
    Measure.absolutelyContinuous_restrict.ae_le hsc
  have hsM : ∀ᵐ x ∂(sphereMeasure t).restrict (K ∩ Hm), x ∈ Metric.sphere t 1 :=
    Measure.absolutelyContinuous_restrict.ae_le hsc
  have htU := SolidGeom.sphere_upper_patch_transport t e he K hK
    (fun p => a + b * u i p) (by fun_prop)
  change (∫ x in K ∩ Hp, (a + b * u i (P x)) * inner ℝ (e 2) (x - t) ∂sphereMeasure t) =
    (∫ p in D i, if X p (u i p) ∈ K then a + b * u i p else 0) at htU
  have hupper : (∫ x in K ∩ Hp, f x ∂sphereMeasure t) =
      ∫ p in D i, if X p (u i p) ∈ K then a + b * u i p else 0 := by
    rw [← htU]
    apply integral_congr_ae
    filter_upwards [hsP, ae_restrict_mem (hK.inter hHp)] with x hs hx
    simp [f, hucoord x hs hx.2]
  let V : ℝ × ℝ → E3 := fun p => p.1 • e 0 + p.2 • e 1 +
    (-inner ℝ (e 2) t + Real.sqrt
      (1 - (p.1 - inner ℝ (e 0) t)^2 - (p.2 - inner ℝ (e 1) t)^2)) • (-e 2)
  have hV (p : ℝ × ℝ) : V p = X p (l i p) := by
    simp [V, X, l, t, smul_neg, ← neg_smul, sub_eq_add_neg]
    congr 1
    ring
  have htL := SolidGeom.sphere_upper_patch_transport t q hq K hK
    (fun p => a + b * l i p) (by fun_prop)
  dsimp only at htL
  simp only [hq0, hq1, hq2, inner_neg_left] at htL
  change (∫ x in K ∩ Hm, (a + b * l i (P x)) * (-inner ℝ (e 2) (x - t)) ∂sphereMeasure t) =
    (∫ p in D i, if V p ∈ K then a + b * l i p else 0) at htL
  simp_rw [hV] at htL
  have heqL : (∫ x in K ∩ Hm, (a + b * l i (P x)) * (-inner ℝ (e 2) (x - t)) ∂sphereMeasure t) =
      -(∫ x in K ∩ Hm, f x ∂sphereMeasure t) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hsM, ae_restrict_mem (hK.inter hHm)] with x hs hx
    simp [f, hlcoord x hs hx.2]
  rw [heqL] at htL
  letI : IsFiniteMeasure (sphereMeasure t) := by unfold sphereMeasure; infer_instance
  have hfc : Continuous f := by fun_prop
  have hfS : IntegrableOn f (Metric.sphere t 1) (sphereMeasure t) :=
    hfc.continuousOn.integrableOn_compact (isCompact_sphere t 1)
  have hf0 : Integrable f (sphereMeasure t) :=
    (hfS.integrable_indicator Metric.isClosed_sphere.measurableSet).congr (by
      filter_upwards [hsc] with x hx
      exact Set.indicator_of_mem hx f)
  have hf : Integrable f ((sphereMeasure t).restrict K) := hf0.integrableOn
  have hsplitfun : f = fun x => Hp.indicator f x + Hm.indicator f x := by
    funext x
    by_cases hp : x ∈ Hp
    · have hm : x ∉ Hm := by dsimp [Hp, Hm] at *; linarith
      simp [hp, hm]
    · by_cases hm : x ∈ Hm
      · simp [hp, hm]
      · have hz : inner ℝ (e 2) (x - t) = 0 := by dsimp [Hp, Hm] at *; linarith
        simp [hp, hm, f, hz]
  have hsplit : (∫ x in K, f x ∂sphereMeasure t) =
      (∫ x in K ∩ Hp, f x ∂sphereMeasure t) +
      (∫ x in K ∩ Hm, f x ∂sphereMeasure t) := by
    calc
      (∫ x in K, f x ∂sphereMeasure t) =
          ∫ x in K, Hp.indicator f x + Hm.indicator f x ∂sphereMeasure t := by
        exact congrArg (fun g => ∫ x in K, g x ∂sphereMeasure t) hsplitfun
      _ = (∫ x in K, Hp.indicator f x ∂sphereMeasure t) +
          (∫ x in K, Hm.indicator f x ∂sphereMeasure t) := integral_add (hf.indicator hHp) (hf.indicator hHm)
      _ = _ := by rw [setIntegral_indicator hHp, setIntegral_indicator hHm]
  rw [hsplit, hupper]
  linarith

#print axioms proof_SolidGeom_ballInter_patch_graph_flux
