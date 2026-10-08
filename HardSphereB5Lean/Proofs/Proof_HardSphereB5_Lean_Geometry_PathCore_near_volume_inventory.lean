import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_incidence
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_coordinate_realization
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_walls_pathMeasure_null
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_pair_width
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_normal_form_volume
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_near_face_inventory
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical

private theorem p7nfi_integral_finite_inventory
    {α ι κ η : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ] [Fintype η]
    (μ : Measure α) (w D : α → ℝ)
    (V E : ι → α → ℝ) (B : κ → η → α → ℝ)
    (cw cv cb ce cd : ℝ)
    (hw : Integrable w μ) (hD : Integrable D μ)
    (hV : ∀ l, Integrable (V l) μ) (hE : ∀ l, Integrable (E l) μ)
    (hB : ∀ i j, Integrable (B i j) μ) :
    (∫ x, cw * w x + cv * (∑ l, V l x) + cb * (∑ i, ∑ j, B i j x) +
      ce * (∑ l, E l x) + cd * D x ∂μ) =
      cw * (∫ x, w x ∂μ) + (∑ l, cv * ∫ x, V l x ∂μ) +
      (∑ i, ∑ j, cb * ∫ x, B i j x ∂μ) +
      (∑ l, ce * ∫ x, E l x ∂μ) + cd * (∫ x, D x ∂μ) := by
  have hVS : Integrable (fun x => ∑ l, V l x) μ :=
    integrable_finsetSum Finset.univ (fun l _ => hV l)
  have hES : Integrable (fun x => ∑ l, E l x) μ :=
    integrable_finsetSum Finset.univ (fun l _ => hE l)
  have hBJ (i : κ) : Integrable (fun x => ∑ j, B i j x) μ :=
    integrable_finsetSum Finset.univ (fun j _ => hB i j)
  have hBS : Integrable (fun x => ∑ i, ∑ j, B i j x) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hBJ i)
  have hvInt : (∫ x, ∑ l, V l x ∂μ) = ∑ l, ∫ x, V l x ∂μ :=
    integral_finsetSum Finset.univ (fun l _ => hV l)
  have heInt : (∫ x, ∑ l, E l x ∂μ) = ∑ l, ∫ x, E l x ∂μ :=
    integral_finsetSum Finset.univ (fun l _ => hE l)
  have hbInt : (∫ x, ∑ i, ∑ j, B i j x ∂μ) = ∑ i, ∑ j, ∫ x, B i j x ∂μ := by
    rw [integral_finsetSum Finset.univ (fun i _ => hBJ i)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hB i j)
  have h01 : Integrable (fun x => cw * w x + cv * (∑ l, V l x)) μ :=
    (hw.const_mul cw).add (hVS.const_mul cv)
  have h012 : Integrable (fun x => cw * w x + cv * (∑ l, V l x) +
      cb * (∑ i, ∑ j, B i j x)) μ := h01.add (hBS.const_mul cb)
  have h0123 : Integrable (fun x => cw * w x + cv * (∑ l, V l x) +
      cb * (∑ i, ∑ j, B i j x) + ce * (∑ l, E l x)) μ :=
    h012.add (hES.const_mul ce)
  rw [integral_add h0123 (hD.const_mul cd), integral_add h012 (hES.const_mul ce),
    integral_add h01 (hBS.const_mul cb), integral_add (hw.const_mul cw) (hVS.const_mul cv)]
  simp only [integral_const_mul]
  rw [hvInt, hbInt, heInt]
  simp only [Finset.mul_sum]

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open MeasureTheory Real
open scoped Classical

noncomputable section
open MeasureTheory Real
open scoped Classical
private lemma p7nar_support_measurable : MeasurableSet support := by
  unfold support
  have hH : Measurable (fun v : Param => Hpoly v.1 v.2.1 v.2.2) := by
    unfold Hpoly
    fun_prop
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
        ((measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
          (measurableSet_lt measurable_const hH))))

open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000

private lemma p7nar_quadratic_arcsin_deriv (a b s : ℝ) (hb : 0 < b) (hs : s∈Set.Ioo (a-b) (a+b)) :
    HasDerivAt (fun s : ℝ => arcsin ((s-a)/b)) (1/√(b^2-(a-s)^2)) s := by
  have hy1 : -1 < (s-a)/b := (lt_div_iff₀ hb).2 (by linarith [hs.1])
  have hy2 : (s-a)/b < 1 := (div_lt_iff₀ hb).2 (by linarith [hs.2])
  have hD : 0 < b^2-(a-s)^2 := by nlinarith [hs.1,hs.2]
  have hi : 1-((s-a)/b)^2=(b^2-(a-s)^2)/(b^2) := by field_simp [hb.ne']; ring
  have ht : √(1-((s-a)/b)^2) = √(b^2-(a-s)^2)/b := by
    rw [hi,Real.sqrt_div hD.le, Real.sqrt_sq hb.le]
  have hd := (Real.hasDerivAt_arcsin (ne_of_gt hy1) (ne_of_lt hy2)).comp s
    (((hasDerivAt_id s).sub_const a).div_const b)
  convert hd using 1 <;> try rfl
  rw [ht]
  field_simp [hb.ne', (Real.sqrt_pos.mpr hD).ne']

private lemma p7nar_quadratic_fiber_integrable (a b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => 1/√(b^2-(a-s)^2)) (Set.Ioo (a-b) (a+b)) := by
  have hc : Continuous (fun s : ℝ => arcsin ((s-a)/b)) := by fun_prop
  have hi := intervalIntegral.integrableOn_deriv_of_nonneg hc.continuousOn
    (fun s hs => p7nar_quadratic_arcsin_deriv a b s hb hs)
    (fun s _ => one_div_nonneg.mpr (sqrt_nonneg _))
  exact hi.mono_set Set.Ioo_subset_Ioc_self

private lemma p7nar_quadratic_fiber_integral (a b : ℝ) (hb : 0 < b) :
    (∫ s in Set.Ioo (a-b) (a+b), (1/√(b^2-(a-s)^2))) = π := by
  have hab : a-b ≤ a+b := by linarith
  have hc : Continuous (fun s : ℝ => arcsin ((s-a)/b)) := by fun_prop
  have hi := p7nar_quadratic_fiber_integrable a b hb
  have hI : IntervalIntegrable (fun s : ℝ => 1/√(b^2-(a-s)^2)) volume (a-b) (a+b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr hi
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc.continuousOn
    (fun s hs => p7nar_quadratic_arcsin_deriv a b s hb hs) hI
  rw [intervalIntegral.integral_of_le hab,integral_Ioc_eq_integral_Ioo] at hh
  have hm : (a-b-a)/b=(-1:ℝ) := by field_simp [hb.ne']; ring
  have hp : (a+b-a)/b=(1:ℝ) := by field_simp [hb.ne']; ring
  rw [hm,hp,arcsin_one,arcsin_neg_one] at hh
  linarith

open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000
private lemma p7nar_b0_pos {X Y : ℝ} (hX : X∈Set.Ioo (0:ℝ) 1) (hY : Y∈Set.Ioo (0:ℝ) 1) : 0 < b0 X Y := by
  have hx : 0 < X*(1-X/4) := mul_pos hX.1 (by linarith [hX.2])
  have hy : 0 < Y*(1-Y/4) := mul_pos hY.1 (by linarith [hY.2])
  unfold b0 rX
  exact mul_pos (mul_pos (by norm_num) (sqrt_pos.mpr hx)) (sqrt_pos.mpr hy)

private lemma p7nar_H_quadratic {X Y : ℝ} (hX : X∈Set.Ioo (0:ℝ) 1) (hY : Y∈Set.Ioo (0:ℝ) 1) (s : ℝ) :
    Hpoly X Y s=(b0 X Y)^2-(a0 X Y-s)^2 := by
  have hx : 0 ≤ X*(1-X/4) := mul_nonneg hX.1.le (by linarith [hX.2])
  have hy : 0 ≤ Y*(1-Y/4) := mul_nonneg hY.1.le (by linarith [hY.2])
  unfold Hpoly b0 rX a0
  rw [show (2*√(X*(1-X/4))*√(Y*(1-Y/4)))^2 = 4*(√(X*(1-X/4)))^2*(√(Y*(1-Y/4)))^2 by ring,
    Real.sq_sqrt hx,Real.sq_sqrt hy]
  ring

private lemma p7nar_H_fiber_set {X Y : ℝ} (hX : X∈Set.Ioo (0:ℝ) 1) (hY : Y∈Set.Ioo (0:ℝ) 1) :
    {s : ℝ | 0<Hpoly X Y s}=Set.Ioo (a0 X Y-b0 X Y) (a0 X Y+b0 X Y) := by
  have hb := p7nar_b0_pos hX hY
  ext s
  rw [Set.mem_setOf_eq,p7nar_H_quadratic hX hY s]
  change 0<(b0 X Y)^2-(a0 X Y-s)^2 ↔ a0 X Y-b0 X Y<s ∧ s<a0 X Y+b0 X Y
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (a0 X Y-s-b0 X Y),sq_nonneg (a0 X Y-s+b0 X Y)]
  · rintro ⟨hl,hr⟩
    nlinarith

private lemma p7nar_path_fiber_mass {X Y : ℝ} (hX : X∈Set.Ioo (0:ℝ) 1) (hY : Y∈Set.Ioo (0:ℝ) 1) :
    (∫⁻ s in {s : ℝ | 0<Hpoly X Y s}, ENNReal.ofReal (π/√(Hpoly X Y s)))=ENNReal.ofReal (π^2) := by
  rw [p7nar_H_fiber_set hX hY]
  simp_rw [p7nar_H_quadratic hX hY]
  have hi := (p7nar_quadratic_fiber_integrable (a0 X Y) (b0 X Y) (p7nar_b0_pos hX hY)).const_mul π
  have hI := p7nar_quadratic_fiber_integral (a0 X Y) (b0 X Y) (p7nar_b0_pos hX hY)
  have heq : (fun s : ℝ => π/√((b0 X Y)^2-(a0 X Y-s)^2)) =
      (fun s => π*(1/√((b0 X Y)^2-(a0 X Y-s)^2))) := by funext s; ring
  have hi' : IntegrableOn (fun s : ℝ => π/√((b0 X Y)^2-(a0 X Y-s)^2))
      (Set.Ioo (a0 X Y-b0 X Y) (a0 X Y+b0 X Y)) := by rw [heq]; exact hi
  rw [← ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ fun s => div_nonneg pi_pos.le (sqrt_nonneg _))]
  have hJ : (∫ s in Set.Ioo (a0 X Y-b0 X Y) (a0 X Y+b0 X Y), π/√((b0 X Y)^2-(a0 X Y-s)^2))=π^2 := by
    rw [heq,integral_const_mul,hI]
    ring
  rw [hJ]

open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000

private def p7nar_fullDensity (v : Param) : ENNReal := support.indicator
  (fun v => ENNReal.ofReal (π/√(Hpoly v.1 v.2.1 v.2.2))) v
private lemma p7nar_fullDensity_measurable : Measurable p7nar_fullDensity := by
  exact (by unfold Hpoly; fun_prop : Measurable (fun v : Param => ENNReal.ofReal (π/√(Hpoly v.1 v.2.1 v.2.2)))).indicator p7nar_support_measurable

private lemma p7nar_fullDensity_fiber (X Y : ℝ) :
    (∫⁻ s : ℝ, p7nar_fullDensity (X,Y,s))=
      (if X∈Set.Ioo (0:ℝ) 1 then (Set.Ioo (0:ℝ) 1).indicator (fun _ => ENNReal.ofReal (π^2)) Y else 0) := by
  by_cases hX : X∈Set.Ioo (0:ℝ) 1
  · rw [if_pos hX]
    by_cases hY : Y∈Set.Ioo (0:ℝ) 1
    · rw [Set.indicator_of_mem hY]
      have heq (s : ℝ) : p7nar_fullDensity (X,Y,s)=
          {s : ℝ | 0<Hpoly X Y s}.indicator (fun s => ENNReal.ofReal (π/√(Hpoly X Y s))) s := by
        simp [p7nar_fullDensity,support,Set.indicator,hX.1,hX.2,hY.1,hY.2]
      simp_rw [heq]
      rw [lintegral_indicator (by unfold Hpoly; measurability)]
      exact p7nar_path_fiber_mass hX hY
    · rw [Set.indicator_of_notMem hY]
      have heq (s : ℝ) : p7nar_fullDensity (X,Y,s)=0 := by
        apply Set.indicator_of_notMem
        exact fun h => hY ⟨h.2.2.1,h.2.2.2.1⟩
      simp_rw [heq]
      simp
  · rw [if_neg hX]
    have heq (s : ℝ) : p7nar_fullDensity (X,Y,s)=0 := by
      apply Set.indicator_of_notMem
      exact fun h => hX ⟨h.1,h.2.1⟩
    simp_rw [heq]
    simp

private lemma p7nar_pathMeasure_total_mass : pathMeasure Set.univ=ENNReal.ofReal (π^2) := by
  unfold pathMeasure
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,←lintegral_indicator p7nar_support_measurable]
  change (∫⁻ v : Param, p7nar_fullDensity v)=ENNReal.ofReal (π^2)
  rw [show (volume : Measure Param)=(volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)) from rfl]
  rw [lintegral_prod _ p7nar_fullDensity_measurable.aemeasurable]
  have hf (X : ℝ) : (∫⁻ p : ℝ×ℝ, p7nar_fullDensity (X,p))=
      (Set.Ioo (0:ℝ) 1).indicator (fun _ => ENNReal.ofReal (π^2)) X := by
    rw [show (volume : Measure (ℝ×ℝ))=(volume : Measure ℝ).prod (volume : Measure ℝ) from rfl]
    rw [lintegral_prod (fun p : ℝ×ℝ => p7nar_fullDensity (X,p)) (p7nar_fullDensity_measurable.comp (measurable_const.prodMk measurable_id)).aemeasurable]
    simp_rw [p7nar_fullDensity_fiber]
    by_cases hx : X∈Set.Ioo (0:ℝ) 1
    · simp only [if_pos hx,Set.indicator_of_mem hx]
      rw [lintegral_indicator measurableSet_Ioo]
      simp
    · simp [hx,Set.indicator]
  change (∫⁻ X : ℝ, (∫⁻ p : ℝ×ℝ, p7nar_fullDensity (X,p)))=ENNReal.ofReal (π^2)
  calc
    _ = ∫⁻ X : ℝ, (Set.Ioo (0:ℝ) 1).indicator (fun _ => ENNReal.ofReal (π^2)) X := lintegral_congr hf
    _ = ENNReal.ofReal (π^2) := by rw [lintegral_indicator measurableSet_Ioo]; simp

private lemma p7nar_pathMeasure_finite : IsFiniteMeasure pathMeasure := by
  constructor
  rw [p7nar_pathMeasure_total_mass]
  exact ENNReal.ofReal_lt_top
private lemma p7nar_nearMeasure_finite : IsFiniteMeasure (pathMeasure.restrict nearDomain) := by
  letI := p7nar_pathMeasure_finite
  infer_instance

private lemma p7n_support_measurable : MeasurableSet support := by
  unfold support Hpoly
  measurability
private lemma p7n_near_measurable : MeasurableSet nearDomain := by
  unfold nearDomain
  measurability
private lemma p7n_path_ae_support : ∀ᵐ v ∂pathMeasure, v ∈ support := by
  unfold pathMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem p7n_support_measurable)
private lemma p7n_path_ae_p4_ne : ∀ᵐ v ∂pathMeasure, P4poly v.1 v.2.1 v.2.2 ≠ 0 := by
  have hw : ∀ᵐ v ∂pathMeasure, v ∉ wallSet := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using walls_pathMeasure_null
  exact hw.mono (fun v hv h => hv (Or.inl h))
private lemma p7n_canonical_config {X Y s : ℝ} (hX : 0 < X) (hX1 : X < 1)
    (hY : 0 < Y) (hY1 : Y < 1) (hH : 0 < Hpoly X Y s) :
    IsPathConfig (canonicalCenters X Y s) X Y s :=
  (coordinate_realization hX hX1 hY hY1 hH).1
private lemma p7n_pathMeasure_finite : IsFiniteMeasure pathMeasure :=
  p7nar_pathMeasure_finite

open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
private def p7n_countSelector (l : Fin 4) (v : Param) : ℝ :=
  if 0<P4poly v.1 v.2.1 v.2.2 then 1 else if 0 < Qpoly v.1 v.2.1 v.2.2 l ∧ Apoly v.1 v.2.1 v.2.2 l < 0 then 2 else 0
private lemma p7n_countSelector_measurable (l : Fin 4) : Measurable (p7n_countSelector l) := by
  have hP : MeasurableSet {v : Param | 0<P4poly v.1 v.2.1 v.2.2} := by exact measurableSet_lt measurable_const (by unfold P4poly; fun_prop)
  have hA' : Measurable (fun v : Param => Apoly v.1 v.2.1 v.2.2 l) := by
    fin_cases l
    · change Measurable (fun v : Param => -v.1^2*v.2.1+v.1*v.2.1*v.2.2+v.1*v.2.1-v.1*v.2.2+v.1-v.2.2^2+2*v.2.2-1)
      fun_prop
    · change Measurable (fun v : Param => -v.1*v.2.1^2+v.1*v.2.1*v.2.2+v.1*v.2.1-v.2.1*v.2.2+v.2.1-v.2.2^2+2*v.2.2-1)
      fun_prop
    · change Measurable (fun v : Param => v.2.1*(-v.1*v.2.1+2*v.1+v.2.2-1))
      fun_prop
    · change Measurable (fun v : Param => v.1*(-v.1*v.2.1+2*v.2.1+v.2.2-1))
      fun_prop
  have hA : MeasurableSet {v : Param | Apoly v.1 v.2.1 v.2.2 l<0} := measurableSet_lt hA' measurable_const
  have hQ' : Measurable (fun v : Param => Qpoly v.1 v.2.1 v.2.2 l) := by
    fin_cases l <;> unfold Qpoly <;> dsimp <;> fun_prop
  have hQ : MeasurableSet {v : Param | 0 < Qpoly v.1 v.2.1 v.2.2 l} :=
    measurableSet_lt measurable_const hQ'
  exact measurable_const.ite hP (measurable_const.ite (hQ.inter hA) measurable_const)
private lemma p7n_count_ae (l : Fin 4) : ∀ᵐ v ∂pathMeasure,
    (nRet (centers v) l : ℝ)=p7n_countSelector l v := by
  filter_upwards [p7n_path_ae_support,p7n_path_ae_p4_ne] with v hv hp
  have hc := p7n_canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  change IsPathConfig (centers v) v.1 v.2.1 v.2.2 at hc
  by_cases hbulk : 0 < P4poly v.1 v.2.1 v.2.2
  · rw [(bulk_incidence hc hbulk).1 l]
    simp [p7n_countSelector, hbulk]
  · have hsliver : P4poly v.1 v.2.1 v.2.2 < 0 :=
      lt_of_le_of_ne (le_of_not_gt hbulk) hp
    rw [(sliver_incidence hc hsliver).1 l]
    unfold p7n_countSelector
    rw [if_neg hbulk]
    split_ifs <;> norm_num
private lemma p7n_count_integrable (l : Fin 4) : Integrable (fun v => (nRet (centers v) l : ℝ)) pathMeasure := by
  letI := p7n_pathMeasure_finite
  have hi : Integrable (p7n_countSelector l) pathMeasure := by
    refine (integrable_const (2:ℝ)).mono' (p7n_countSelector_measurable l).aestronglyMeasurable
      (ae_of_all _ fun v => ?_)
    unfold p7n_countSelector
    split_ifs <;> norm_num
  exact hi.congr ((p7n_count_ae l).mono fun v h => h.symm)
private lemma p7n_weight_integrable : Integrable weight pathMeasure := by
  letI := p7n_pathMeasure_finite
  refine (integrable_const (1:ℝ)).mono' (by unfold weight; fun_prop)
    (p7n_path_ae_support.mono fun v hv => ?_)
  unfold weight
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [hv.1,hv.2.2.1])]
  linarith [hv.2.1,hv.2.2.2.1]
private lemma p7n_centers_measurable : Measurable centers := by
  unfold centers canonicalCenters rX a0 Hpoly
  fun_prop
private lemma p7n_beta_measurable (i j k : Fin 4) : Measurable (fun v => betaA (centers v) i j k) := by
  have hc (l : Fin 4) : Measurable (fun v => centers v l) := (measurable_pi_apply l).comp p7n_centers_measurable
  have hci := hc i; have hcj := hc j; have hck := hc k
  unfold betaA atan2 Qf QT DeltaT q
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop
private lemma p7n_phi_measurable (i j : Fin 4) : Measurable (fun v => phiE (centers v) i j) := by
  have hc (l : Fin 4) : Measurable (fun v => centers v l) := (measurable_pi_apply l).comp p7n_centers_measurable
  have hci := hc i; have hcj := hc j; have hck := hc (oth1 i j); have hcl := hc (oth2 i j)
  unfold phiE dihedral InnerProductGeometry.angle perpProj
  fun_prop
private lemma p7n_beta_integrable (i j k : Fin 4) : Integrable (fun v => betaA (centers v) i j k) pathMeasure := by
  letI := p7n_pathMeasure_finite
  refine (integrable_const π).mono' (p7n_beta_measurable i j k).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  exact Complex.abs_arg_le_pi _
private lemma p7n_phi_integrable (i j : Fin 4) : Integrable (fun v => phiE (centers v) i j) pathMeasure := by
  letI := p7n_pathMeasure_finite
  refine (integrable_const π).mono' (p7n_phi_measurable i j).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  unfold phiE dihedral
  rw [Real.norm_eq_abs,abs_of_nonneg (InnerProductGeometry.angle_nonneg _ _)]
  exact InnerProductGeometry.angle_le_pi _ _

open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000
private lemma p7n_weight_bound (v : Param) (hv : v∈support) : ‖weight v‖≤1 := by
  unfold weight
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [hv.1,hv.2.2.1])]
  linarith [hv.2.1,hv.2.2.2.1]
private lemma p7n_count_bound_ae (l : Fin 4) : ∀ᵐ v ∂pathMeasure, ‖(nRet (centers v) l : ℝ)‖≤2 := by
  filter_upwards [p7n_count_ae l] with v hv
  rw [hv]
  unfold p7n_countSelector
  split_ifs <;> norm_num
private lemma p7n_near_dist_bound (v : Param) (hv : v∈support) (hs : v∈nearDomain) (i j : Fin 4) :
    dist (centers v i) (centers v j)≤1 := by
  have hc := p7n_canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  have h01 := hc.q01.le; have h02 := hc.q02.le
  have h03 := hc.q03.le.trans hv.2.2.2.1.le
  have h12 := hc.q12.le.trans hv.2.1.le
  have h13 := hc.q13.le; have h23 := hc.q23.le.trans hs.le
  have hqs (a b : Fin 4) : q (centers v) a b=q (centers v) b a := by unfold q; exact congrArg (fun z : ℝ => z^2) (dist_comm (centers v a) (centers v b))
  have hq : q (centers v) i j ≤ 1 := by
    fin_cases i <;> fin_cases j
    · simp [q]
    · exact h01
    · exact h02
    · exact h03
    · exact (hqs 1 0).le.trans h01
    · simp [q]
    · exact h12
    · exact h13
    · exact (hqs 2 0).le.trans h02
    · exact (hqs 2 1).le.trans h12
    · simp [q]
    · exact h23
    · exact (hqs 3 0).le.trans h03
    · exact (hqs 3 1).le.trans h13
    · exact (hqs 3 2).le.trans h23
    · simp [q]
  unfold q at hq
  nlinarith [(dist_nonneg : 0≤dist (centers v i) (centers v j))]
private lemma p7n_g_bound {d : ℝ} (hd0 : 0≤d) (hd1 : d≤1) : ‖g d‖≤2 := by
  have h3 : 0≤d^3 := pow_nonneg hd0 _
  have h31 : d^3≤1 := pow_le_one₀ hd0 hd1
  rw [Real.norm_eq_abs]
  unfold g
  exact abs_le.mpr ⟨by linarith,by linarith⟩
private lemma p7n_g_measurable (i j : Fin 4) : Measurable (fun v => g (dist (centers v i) (centers v j))) := by
  have hi := (measurable_pi_apply i).comp p7n_centers_measurable
  have hj := (measurable_pi_apply j).comp p7n_centers_measurable
  unfold g
  fun_prop
private lemma p7n_g_near_bound_ae (i j : Fin 4) : ∀ᵐ v ∂pathMeasure.restrict nearDomain,
    ‖g (dist (centers v i) (centers v j))‖≤2 := by
  filter_upwards [ae_restrict_of_ae p7n_path_ae_support,ae_restrict_mem p7n_near_measurable] with v hv hs
  exact p7n_g_bound dist_nonneg (p7n_near_dist_bound v hv hs i j)
private lemma p7n_weighted_triangle_integrable (i j k l : Fin 4) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*(nRet (centers v) l : ℝ)*betaA (centers v) i j k)
      nearDomain pathMeasure := by
  have hb : IntegrableOn (fun v => betaA (centers v) i j k) nearDomain pathMeasure := (p7n_beta_integrable i j k).restrict
  have hc : IntegrableOn (fun v => (nRet (centers v) l : ℝ)) nearDomain pathMeasure := (p7n_count_integrable l).restrict
  have hB := hb.bdd_mul hc.aestronglyMeasurable (ae_restrict_of_ae (p7n_count_bound_ae l))
  have hG := hB.bdd_mul (p7n_g_measurable i j).aestronglyMeasurable (p7n_g_near_bound_ae i j)
  have hW : AEStronglyMeasurable weight (pathMeasure.restrict nearDomain) := p7n_weight_integrable.restrict.aestronglyMeasurable
  have h := hG.bdd_mul hW ((ae_restrict_of_ae p7n_path_ae_support).mono fun v hv => p7n_weight_bound v hv)
  simpa only [IntegrableOn,mul_assoc] using h
private lemma p7n_weighted_phi_integrable (i j : Fin 4) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*phiE (centers v) i j)
      nearDomain pathMeasure := by
  have hp : IntegrableOn (fun v => phiE (centers v) i j) nearDomain pathMeasure := (p7n_phi_integrable i j).restrict
  have hG := hp.bdd_mul (p7n_g_measurable i j).aestronglyMeasurable (p7n_g_near_bound_ae i j)
  have h := hG.bdd_mul p7n_weight_integrable.restrict.aestronglyMeasurable
    ((ae_restrict_of_ae p7n_path_ae_support).mono fun v hv => p7n_weight_bound v hv)
  simpa only [IntegrableOn,mul_assoc] using h
private lemma p7n_weighted_bulk_integrable (i j : Fin 4) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*phiE (centers v) i j)
      nearBulk pathMeasure :=
  (p7n_weighted_phi_integrable i j).mono_set (fun _ hv => hv.1)

open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000

private def p7n_commonSelector (i j : Fin 4) (v : Param) : Prop :=
  p7n_countSelector (oth1 i j) v≠0 ∧ p7n_countSelector (oth2 i j) v≠0
private lemma p7n_commonSelector_measurable (i j : Fin 4) : MeasurableSet {v : Param | p7n_commonSelector i j v} :=
  ((measurableSet_eq_fun (p7n_countSelector_measurable (oth1 i j)) measurable_const).compl).inter
    (measurableSet_eq_fun (p7n_countSelector_measurable (oth2 i j)) measurable_const).compl
private lemma p7n_common_ae (i j : Fin 4) : ∀ᵐ v ∂pathMeasure,
    isCommon (centers v) i j ↔ p7n_commonSelector i j v := by
  filter_upwards [p7n_count_ae (oth1 i j),p7n_count_ae (oth2 i j)] with v h1 h2
  unfold isCommon p7n_commonSelector
  rw [←h1,←h2]
  norm_cast
private lemma p7n_correction_angle_integrable (i j : Fin 4) :
    Integrable (fun v => if P4poly v.1 v.2.1 v.2.2<0 ∧ isCommon (centers v) i j then 2*π else 0) pathMeasure := by
  letI := p7n_pathMeasure_finite
  let t : Set Param := {v | P4poly v.1 v.2.1 v.2.2<0 ∧ p7n_commonSelector i j v}
  have hP : MeasurableSet {v : Param | P4poly v.1 v.2.1 v.2.2<0} := by unfold P4poly; measurability
  have ht : MeasurableSet t := hP.inter (p7n_commonSelector_measurable i j)
  have hi : Integrable (t.indicator (fun _ : Param => 2*π)) pathMeasure := (integrable_const (2*π)).indicator ht
  refine hi.congr ?_
  filter_upwards [p7n_common_ae i j] with v hv
  simp only [t,Set.indicator,Set.mem_setOf_eq,hv]
private lemma p7n_weighted_correction_integrable (i j : Fin 4) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if P4poly v.1 v.2.1 v.2.2<0 ∧ isCommon (centers v) i j then 2*π else 0)) nearDomain pathMeasure := by
  have hc : Integrable (fun v => if P4poly v.1 v.2.1 v.2.2<0 ∧ isCommon (centers v) i j then 2*π else 0)
      (pathMeasure.restrict nearDomain) := (p7n_correction_angle_integrable i j).restrict
  have hG := hc.bdd_mul (p7n_g_measurable i j).aestronglyMeasurable (p7n_g_near_bound_ae i j)
  have h := hG.bdd_mul p7n_weight_integrable.restrict.aestronglyMeasurable
    ((ae_restrict_of_ae p7n_path_ae_support).mono fun v hv => p7n_weight_bound v hv)
  simpa only [IntegrableOn,mul_assoc] using h
private lemma p7n_conditional_phi_integrable (i j : Fin 4) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if 0<P4poly v.1 v.2.1 v.2.2 then phiE (centers v) i j else 0)) nearDomain pathMeasure := by
  have hP : MeasurableSet {v : Param | 0<P4poly v.1 v.2.1 v.2.2} := by unfold P4poly; measurability
  have hf : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*phiE (centers v) i j)
      (pathMeasure.restrict nearDomain) := p7n_weighted_phi_integrable i j
  have hi := hf.indicator hP
  have heq : (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if 0<P4poly v.1 v.2.1 v.2.2 then phiE (centers v) i j else 0)) =
      {v : Param | 0<P4poly v.1 v.2.1 v.2.2}.indicator
        (fun v => weight v*g (dist (centers v i) (centers v j))*phiE (centers v) i j) := by
    funext v
    by_cases h : 0<P4poly v.1 v.2.1 v.2.2 <;> simp [Set.indicator,h]
  change Integrable _ (pathMeasure.restrict nearDomain)
  rw [heq]
  exact hi

private theorem p7n_pair_arc_integrable_of_pair_width
    (hWidth : ∀ {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s)
      (hP : P4poly X Y s≠0) (i j : Fin 4) (hij : i≠j),
      ell c i j = (nRet c (oth2 i j) : ℝ)*betaA c i j (oth1 i j)
        + (nRet c (oth1 i j) : ℝ)*betaA c i j (oth2 i j)
        - (if 0<P4poly X Y s then phiE c i j else 0)
        - (if P4poly X Y s<0 ∧ isCommon c i j then 2*π else 0))
    (i j : Fin 4) (hij : i≠j) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*ell (centers v) i j)
      nearDomain pathMeasure := by
  let μ := pathMeasure.restrict nearDomain
  have hA : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*
      (nRet (centers v) (oth2 i j) : ℝ)*betaA (centers v) i j (oth1 i j)) μ :=
    p7n_weighted_triangle_integrable i j (oth1 i j) (oth2 i j)
  have hB : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*
      (nRet (centers v) (oth1 i j) : ℝ)*betaA (centers v) i j (oth2 i j)) μ :=
    p7n_weighted_triangle_integrable i j (oth2 i j) (oth1 i j)
  have hP : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if 0<P4poly v.1 v.2.1 v.2.2 then phiE (centers v) i j else 0)) μ := p7n_conditional_phi_integrable i j
  have hC : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if P4poly v.1 v.2.1 v.2.2<0 ∧ isCommon (centers v) i j then 2*π else 0)) μ := p7n_weighted_correction_integrable i j
  change Integrable _ μ
  refine (((hA.add hB).sub hP).sub hC).congr ?_
  filter_upwards [ae_restrict_of_ae p7n_path_ae_support,ae_restrict_of_ae p7n_path_ae_p4_ne] with v hv hp
  have hc := p7n_canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  change IsPathConfig (centers v) v.1 v.2.1 v.2.2 at hc
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [hWidth hc hp i j hij]
  ring
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical

private lemma p7n_gamma_measurable (i j k : Fin 4) :
    Measurable (fun v => gammaA (centers v) i j k) := by
  have hc (l : Fin 4) : Measurable (fun v => centers v l) :=
    (measurable_pi_apply l).comp p7n_centers_measurable
  have hci := hc i; have hcj := hc j; have hck := hc k
  unfold gammaA atan2 Qf QT DeltaT q
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop
private lemma p7n_gamma_integrable (i j k : Fin 4) :
    Integrable (fun v => gammaA (centers v) i j k) pathMeasure := by
  letI := p7n_pathMeasure_finite
  refine (integrable_const π).mono' (p7n_gamma_measurable i j k).aestronglyMeasurable
    (ae_of_all _ (fun v => ?_))
  exact Complex.abs_arg_le_pi _
private lemma p7n_sigma_integrable (l : Fin 4) :
    Integrable (fun v => sigmaF (centers v) l) pathMeasure := by
  exact ((p7n_gamma_integrable (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2).add
    (p7n_gamma_integrable (faceVerts l).2.1 (faceVerts l).1 (faceVerts l).2.2)).add
    (p7n_gamma_integrable (faceVerts l).2.2 (faceVerts l).1 (faceVerts l).2.1)
private lemma p7n_weighted_sigma_integrable (l : Fin 4) :
    IntegrableOn (fun v => weight v * (nRet (centers v) l : ℝ) * sigmaF (centers v) l)
      nearDomain pathMeasure := by
  have hS := (p7n_sigma_integrable l).restrict (s := nearDomain)
  have hN := hS.bdd_mul (p7n_count_integrable l).restrict.aestronglyMeasurable
    (ae_restrict_of_ae (p7n_count_bound_ae l))
  have hW := hN.bdd_mul p7n_weight_integrable.restrict.aestronglyMeasurable
    ((ae_restrict_of_ae p7n_path_ae_support).mono (fun v hv => p7n_weight_bound v hv))
  simpa only [IntegrableOn, mul_assoc] using hW

private lemma p7n_q_near_le_one (v : Param) (hv : v ∈ support) (hs : v ∈ nearDomain) (i j : Fin 4) :
    q (centers v) i j ≤ 1 := by
  have hd := p7n_near_dist_bound v hv hs i j
  unfold q
  nlinarith [(dist_nonneg : 0 ≤ dist (centers v i) (centers v j))]
private lemma p7n_Qface_near_le_four (v : Param) (hv : v ∈ support) (hs : v ∈ nearDomain) (l : Fin 4) :
    Qface (centers v) l ≤ 4 := by
  let i := (faceVerts l).1
  let j := (faceVerts l).2.1
  let k := (faceVerts l).2.2
  have ha : q (centers v) i j ≤ 1 := p7n_q_near_le_one v hv hs i j
  have hb : q (centers v) i k ≤ 1 := p7n_q_near_le_one v hv hs i k
  have hab : q (centers v) i j * q (centers v) i k ≤ 1 := by
    calc
      _ ≤ 1 * q (centers v) i k := mul_le_mul_of_nonneg_right ha (sq_nonneg _)
      _ ≤ 1 := by simpa using hb
  have hprod : 0 ≤ q (centers v) i j * q (centers v) i k * q (centers v) j k :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  change QT (q (centers v) i j) (q (centers v) i k) (q (centers v) j k) ≤ 4
  unfold QT DeltaT
  nlinarith [sq_nonneg (q (centers v) i j + q (centers v) i k - q (centers v) j k)]
private lemma p7n_sqrt_Qface_integrable (l : Fin 4) :
    IntegrableOn (fun v => √(Qface (centers v) l)) nearDomain pathMeasure := by
  letI := p7n_pathMeasure_finite
  have hm : Measurable (fun v => √(Qface (centers v) l)) := by
    have hc (i : Fin 4) : Measurable (fun v => centers v i) :=
      (measurable_pi_apply i).comp p7n_centers_measurable
    unfold Qface Qf QT DeltaT q
    fun_prop
  refine (integrable_const (2 : ℝ)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae p7n_path_ae_support, ae_restrict_mem p7n_near_measurable]
    with v hv hs
  rw [Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)]
  have h := sqrt_le_sqrt (p7n_Qface_near_le_four v hv hs l)
  norm_num at h
  exact h
private lemma p7n_weighted_root_integrable (l : Fin 4) :
    IntegrableOn (fun v => weight v * (nRet (centers v) l : ℝ) * √(Qface (centers v) l))
      nearDomain pathMeasure := by
  have hR := p7n_sqrt_Qface_integrable l
  have hN := hR.bdd_mul (p7n_count_integrable l).restrict.aestronglyMeasurable
    (ae_restrict_of_ae (p7n_count_bound_ae l))
  have hW := hN.bdd_mul p7n_weight_integrable.restrict.aestronglyMeasurable
    ((ae_restrict_of_ae p7n_path_ae_support).mono (fun v hv => p7n_weight_bound v hv))
  simpa only [IntegrableOn, mul_assoc] using hW

private lemma p7n_H_near_le_nine (v : Param) (hv : v ∈ support) (hs : v ∈ nearDomain) :
    Hpoly v.1 v.2.1 v.2.2 ≤ 9 := by
  have hc := p7n_canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  have hs0 : 0 ≤ v.2.2 := hc.q23 ▸ sq_nonneg _
  have hXY : v.1 * v.2.1 ≤ 1 := by
    calc
      _ ≤ 1 * v.2.1 := mul_le_mul_of_nonneg_right hv.2.1.le hv.2.2.1.le
      _ ≤ 1 := by simpa using hv.2.2.2.1.le
  have hsXY : v.2.2 * v.1 * v.2.1 ≤ 1 := by
    calc
      _ = v.2.2 * (v.1 * v.2.1) := by ring
      _ ≤ 1 * (v.1 * v.2.1) :=
        mul_le_mul_of_nonneg_right hs.le (mul_nonneg hv.1.le hv.2.2.1.le)
      _ ≤ 1 := by simpa using hXY
  unfold Hpoly
  nlinarith [sq_nonneg v.2.2,
    mul_nonneg (sq_nonneg v.1) hv.2.2.1.le,
    mul_nonneg hv.1.le (sq_nonneg v.2.1)]
private lemma p7n_sqrt_H_integrable :
    IntegrableOn (fun v => √(Hpoly v.1 v.2.1 v.2.2)) nearDomain pathMeasure := by
  letI := p7n_pathMeasure_finite
  have hm : Measurable (fun v : Param => √(Hpoly v.1 v.2.1 v.2.2)) := by
    unfold Hpoly
    fun_prop
  refine (integrable_const (3 : ℝ)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae p7n_path_ae_support, ae_restrict_mem p7n_near_measurable]
    with v hv hs
  rw [Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)]
  have h := sqrt_le_sqrt (p7n_H_near_le_nine v hv hs)
  norm_num at h
  exact h
private lemma p7n_conditional_H_integrable :
    IntegrableOn (fun v => if 0 < P4poly v.1 v.2.1 v.2.2 then
      weight v * √(Hpoly v.1 v.2.1 v.2.2) else 0) nearDomain pathMeasure := by
  have hP : MeasurableSet {v : Param | 0 < P4poly v.1 v.2.1 v.2.2} := by
    unfold P4poly
    measurability
  have hW := p7n_sqrt_H_integrable.bdd_mul p7n_weight_integrable.restrict.aestronglyMeasurable
    ((ae_restrict_of_ae p7n_path_ae_support).mono (fun v hv => p7n_weight_bound v hv))
  exact hW.indicator hP

private lemma p7n_pair_arc_integrable (i j : Fin 4) (hij : i ≠ j) :
    IntegrableOn (fun v => weight v * g (dist (centers v i) (centers v j)) * ell (centers v) i j)
      nearDomain pathMeasure :=
  p7n_pair_arc_integrable_of_pair_width (fun hc hP i j hij => pair_width hc hP i j hij) i j hij

private lemma p7n_bulk_indicator_integral :
    (∫ v in nearDomain, (if 0 < P4poly v.1 v.2.1 v.2.2 then
      weight v * √(Hpoly v.1 v.2.1 v.2.2) else 0) ∂pathMeasure) =
      ∫ v in nearBulk, weight v * √(Hpoly v.1 v.2.1 v.2.2) ∂pathMeasure := by
  have hP : MeasurableSet {v : Param | 0 < P4poly v.1 v.2.1 v.2.2} := by
    unfold P4poly
    measurability
  change (∫ v in nearDomain,
    {v : Param | 0 < P4poly v.1 v.2.1 v.2.2}.indicator
      (fun v => weight v * √(Hpoly v.1 v.2.1 v.2.2)) v ∂pathMeasure) = _
  rw [setIntegral_indicator hP]
  rfl

private lemma p7n_weighted_normal_form_ae
    :
    (fun v => weight v * vol (centers v) Finset.univ) =ᵐ[pathMeasure.restrict nearDomain]
      (fun v => (8 * π / 3) * weight v + (-1 / 3) *
        (∑ l, weight v * (nRet (centers v) l : ℝ) * sigmaF (centers v) l) +
        (-1 / 2) * (∑ i, ∑ j, (if i < j then
          weight v * g (dist (centers v i) (centers v j)) * ell (centers v) i j else 0)) +
        (1 / 12) * (∑ l, weight v * (nRet (centers v) l : ℝ) * √(Qface (centers v) l)) +
        (-1 / 12) * (if 0 < P4poly v.1 v.2.1 v.2.2 then
          weight v * √(Hpoly v.1 v.2.1 v.2.2) else 0)) := by
  filter_upwards [ae_restrict_of_ae p7n_path_ae_support, ae_restrict_of_ae p7n_path_ae_p4_ne]
    with v hv hp
  have hc := p7n_canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  change IsPathConfig (centers v) v.1 v.2.1 v.2.2 at hc
  rw [HardSphereB5.Lean.Geometry.PathCore.normal_form_volume hc hp]
  have hV : weight v * (∑ l, (nRet (centers v) l : ℝ) * sigmaF (centers v) l) =
      ∑ l, weight v * (nRet (centers v) l : ℝ) * sigmaF (centers v) l := by
    simp only [Finset.mul_sum, mul_assoc]
  have hE : weight v * (∑ l, (nRet (centers v) l : ℝ) * √(Qface (centers v) l)) =
      ∑ l, weight v * (nRet (centers v) l : ℝ) * √(Qface (centers v) l) := by
    simp only [Finset.mul_sum, mul_assoc]
  have hB : weight v * (∑ i, ∑ j,
      (if i < j then g (dist (centers v i) (centers v j)) * ell (centers v) i j else 0)) =
      ∑ i, ∑ j, (if i < j then
        weight v * g (dist (centers v i) (centers v j)) * ell (centers v) i j else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hD : weight v * (if 0 < P4poly v.1 v.2.1 v.2.2 then
      √(Hpoly v.1 v.2.1 v.2.2) / 12 else 0) =
      (1 / 12) * (if 0 < P4poly v.1 v.2.1 v.2.2 then
        weight v * √(Hpoly v.1 v.2.1 v.2.2) else 0) := by
    split_ifs <;> ring
  calc
    _ = (8 * π / 3) * weight v + (-1 / 3) *
        (weight v * (∑ l, (nRet (centers v) l : ℝ) * sigmaF (centers v) l)) +
        (-1 / 2) * (weight v * (∑ i, ∑ j,
          (if i < j then g (dist (centers v i) (centers v j)) * ell (centers v) i j else 0))) +
        (1 / 12) * (weight v * (∑ l, (nRet (centers v) l : ℝ) * √(Qface (centers v) l))) -
        weight v * (if 0 < P4poly v.1 v.2.1 v.2.2 then
          √(Hpoly v.1 v.2.1 v.2.2) / 12 else 0) := by ring
    _ = _ := by rw [hV, hB, hE, hD]; ring

private theorem p7n_near_volume_inventory_of_deps
    :
    Kcap = 2 * Vadj + 2 * Vnon + Ccap + Dcap + 2 * Eadj + 2 * Enon +
      (∑ i, ∑ j, (if i < j then nearPairArc i j else 0)) := by
  let μ := pathMeasure.restrict nearDomain
  let V : Fin 4 → Param → ℝ :=
    fun l v => weight v * (nRet (centers v) l : ℝ) * sigmaF (centers v) l
  let E : Fin 4 → Param → ℝ :=
    fun l v => weight v * (nRet (centers v) l : ℝ) * √(Qface (centers v) l)
  let B : Fin 4 → Fin 4 → Param → ℝ := fun i j v =>
    if i < j then weight v * g (dist (centers v i) (centers v j)) * ell (centers v) i j else 0
  let D : Param → ℝ := fun v => if 0 < P4poly v.1 v.2.1 v.2.2 then
    weight v * √(Hpoly v.1 v.2.1 v.2.2) else 0
  have hB (i j : Fin 4) : Integrable (B i j) μ := by
    by_cases hij : i < j
    · simpa only [B, if_pos hij, IntegrableOn, μ] using p7n_pair_arc_integrable i j (ne_of_lt hij)
    · have he : B i j = (0 : Param → ℝ) := by funext v; simp [B, hij]
      rw [he]
      exact integrable_zero Param ℝ μ
  have hsplit := p7nfi_integral_finite_inventory μ weight D V E B
    (8 * π / 3) (-1 / 3) (-1 / 2) (1 / 12) (-1 / 12)
    p7n_weight_integrable.restrict p7n_conditional_H_integrable
    p7n_weighted_sigma_integrable p7n_weighted_root_integrable hB
  have hC : (8 * π / 3) * (∫ v, weight v ∂μ) = Ccap := rfl
  have hV (l : Fin 4) : (-1 / 3) * (∫ v, V l v ∂μ) = VfaceIntegral l := rfl
  have hE (l : Fin 4) : (1 / 12) * (∫ v, E l v ∂μ) = EfaceIntegral l := rfl
  have hBij (i j : Fin 4) : (-1 / 2) * (∫ v, B i j v ∂μ) =
      (if i < j then nearPairArc i j else 0) := by
    by_cases hij : i < j <;> simp [B, μ, hij, nearPairArc]
  have hD : (-1 / 12) * (∫ v, D v ∂μ) = Dcap := by
    change (-1 / 12) * (∫ v in nearDomain, (if 0 < P4poly v.1 v.2.1 v.2.2 then
      weight v * √(Hpoly v.1 v.2.1 v.2.2) else 0) ∂pathMeasure) = _
    rw [p7n_bulk_indicator_integral]
    rfl
  simp_rw [hC, hV, hBij, hE, hD] at hsplit
  have hK : Kcap = ∫ v, (8 * π / 3) * weight v + (-1 / 3) * (∑ l, V l v) +
      (-1 / 2) * (∑ i, ∑ j, B i j v) + (1 / 12) * (∑ l, E l v) +
      (-1 / 12) * D v ∂μ := by
    exact integral_congr_ae (p7n_weighted_normal_form_ae )
  rw [near_face_inventory.1, near_face_inventory.2] at hsplit
  calc
    Kcap = _ := hK.trans hsplit
    _ = _ := by ring

theorem proof_HardSphereB5_Lean_Geometry_PathCore_near_volume_inventory : Kcap=2*Vadj+2*Vnon+Ccap+Dcap+2*Eadj+2*Enon +
  (∑ i, ∑ j, (if i<j then nearPairArc i j else 0)) :=
  p7n_near_volume_inventory_of_deps #print axioms proof_HardSphereB5_Lean_Geometry_PathCore_near_volume_inventory
