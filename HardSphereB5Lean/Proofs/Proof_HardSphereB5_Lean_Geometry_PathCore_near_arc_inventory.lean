import Mathlib
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_pair_width
import HardSphereB5Lean.Definitions.Def_SolidGeom_ClassicalInputs_SurfaceCalculusInputs
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_bulk_incidence
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_incidence
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_table
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_adjacent_unit_halfwidths
set_option autoImplicit false
noncomputable section
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 2500000

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
private lemma HardSphereB5.Lean.Geometry.PathCore.q_symm' (c : Fin 4 → Pt) (i j : Fin 4) : q c i j = q c j i := by
  simp only [q, dist_comm]

private lemma HardSphereB5.Lean.Geometry.PathCore.inner_from_q (c : Fin 4 → Pt) (i j k : Fin 4) :
    inner ℝ (c j - c i) (c k - c i) = (q c i j + q c i k - q c j k) / 2 := by
  have h := norm_sub_sq_real (c j - c i) (c k - c i)
  have hv : (c j - c i) - (c k - c i) = c j - c k := by abel
  rw [hv] at h
  simp only [q, dist_eq_norm] at ⊢
  rw [norm_sub_rev (c i) (c j), norm_sub_rev (c i) (c k)]
  linarith

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
set_option maxHeartbeats 1000000

private def HardSphereB5.Lean.Geometry.PathCore.swapXY : Param ≃ᵐ Param where
  toEquiv := {
    toFun := fun v => (v.2.1, v.1, v.2.2)
    invFun := fun v => (v.2.1, v.1, v.2.2)
    left_inv := by rintro ⟨x,y,s⟩; rfl
    right_inv := by rintro ⟨x,y,s⟩; rfl }
  measurable_toFun := by
    change Measurable (fun v : Param => (v.2.1,v.1,v.2.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun v : Param => (v.2.1,v.1,v.2.2))
    fun_prop

@[simp] private lemma swapXY_apply (v : Param) : swapXY v = (v.2.1,v.1,v.2.2) := rfl
@[simp] private lemma swapXY_twice (v : Param) : swapXY (swapXY v) = v := by cases v; rfl
private lemma HardSphereB5.Lean.Geometry.PathCore.H_swap (X Y s : ℝ) : Hpoly Y X s = Hpoly X Y s := by unfold Hpoly; ring
private lemma HardSphereB5.Lean.Geometry.PathCore.P4_swap (X Y s : ℝ) : P4poly Y X s = P4poly X Y s := by unfold P4poly; ring
@[simp] private lemma weight_swap (v : Param) : weight (swapXY v) = weight v := by unfold weight; simp; ring
private lemma HardSphereB5.Lean.Geometry.PathCore.swap_support : swapXY ⁻¹' support = support := by
  ext v
  simp only [Set.mem_preimage, support, Set.mem_setOf_eq, swapXY_apply, H_swap]
  tauto
private lemma HardSphereB5.Lean.Geometry.PathCore.swap_near : swapXY ⁻¹' nearDomain = nearDomain := rfl
private lemma HardSphereB5.Lean.Geometry.PathCore.swap_sliver : swapXY ⁻¹' nearSliver = nearSliver := by
  ext v
  simp [nearSliver, P4_swap]
private lemma HardSphereB5.Lean.Geometry.PathCore.support_measurable : MeasurableSet support := by
  unfold support Hpoly
  measurability
private lemma HardSphereB5.Lean.Geometry.PathCore.near_measurable : MeasurableSet nearDomain := by unfold nearDomain; measurability
private lemma HardSphereB5.Lean.Geometry.PathCore.sliver_measurable : MeasurableSet nearSliver := by unfold nearSliver P4poly; measurability

private lemma HardSphereB5.Lean.Geometry.PathCore.swap_volume : MeasurePreserving swapXY (volume : Measure Param) volume := by
  have ha : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ Param) :=
    volume_preserving_prodAssoc
  have hb : MeasurePreserving (Prod.map Prod.swap id : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).prod
      (MeasurePreserving.id (volume : Measure ℝ))
  exact ha.comp (hb.comp (ha.symm MeasurableEquiv.prodAssoc))

private lemma HardSphereB5.Lean.Geometry.PathCore.swap_pathMeasure : MeasurePreserving swapXY pathMeasure pathMeasure := by
  have hb : MeasurePreserving swapXY (volume.restrict support) (volume.restrict support) := by
    simpa only [swap_support] using swap_volume.restrict_preimage support_measurable
  refine ⟨swapXY.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply swapXY.measurable hs]
  unfold pathMeasure
  rw [withDensity_apply _ (swapXY.measurable hs), withDensity_apply _ hs]
  have hi := (hb.restrict_preimage hs).lintegral_comp_emb swapXY.measurableEmbedding
    (fun v : Param => ENNReal.ofReal (π / √(Hpoly v.1 v.2.1 v.2.2)))
  simpa only [swapXY_apply, H_swap] using hi

private lemma HardSphereB5.Lean.Geometry.PathCore.swap_nearMeasure : MeasurePreserving swapXY (pathMeasure.restrict nearDomain)
    (pathMeasure.restrict nearDomain) := by
  simpa only [swap_near] using swap_pathMeasure.restrict_preimage near_measurable
private lemma HardSphereB5.Lean.Geometry.PathCore.swap_sliverMeasure : MeasurePreserving swapXY (pathMeasure.restrict nearSliver)
    (pathMeasure.restrict nearSliver) := by
  simpa only [swap_sliver] using swap_pathMeasure.restrict_preimage sliver_measurable

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
set_option maxHeartbeats 1000000
private lemma HardSphereB5.Lean.Geometry.PathCore.canonical_config {X Y s : ℝ} (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < Hpoly X Y s) : IsPathConfig (canonicalCenters X Y s) X Y s := by
  have hr : 0 < X * (1 - X / 4) := mul_pos hX (by linarith)
  let b : ℝ := rX X
  have hb : 0 < b := Real.sqrt_pos.2 hr
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hb2 : b ^ 2 = X - X ^ 2 / 4 := by
    have h := Real.sq_sqrt hr.le
    change (rX X)^2 = X - X^2/4
    dsimp [rX] at *
    nlinarith only [h]
  let t : ℝ := a0 X Y - s
  let f : ℝ := t / (2 * b)
  let z : ℝ := √(Hpoly X Y s) / (2 * b)
  have hz2 : z ^ 2 = Hpoly X Y s / (4 * b ^ 2) := by
    dsimp [z]
    rw [div_pow, Real.sq_sqrt hH.le]
    ring
  have hf2 : f ^ 2 = t ^ 2 / (4 * b ^ 2) := by dsimp [f]; ring
  have hbf : 2 * b * f = 1 - s + X * Y / 2 := by
    dsimp [f,t,a0]
    field_simp [hb0]
    <;> ring
  have hid : t ^ 2 + Hpoly X Y s = (Y - Y ^ 2 / 4) * (4 * b ^ 2) := by
    dsimp [t,a0]
    rw [hb2]
    unfold Hpoly
    ring
  have hd : f ^ 2 + z ^ 2 + (Y / 2) ^ 2 = Y := by
    calc
      f ^ 2 + z ^ 2 + (Y / 2) ^ 2 =
          (t ^ 2 + Hpoly X Y s) / (4 * b ^ 2) + (Y / 2) ^ 2 := by rw [hf2,hz2]; ring
      _ = Y := by
        rw [hid]
        clear hX hX1 hY hY1 hH hr hb hb2 hz2 hf2 hbf hid
        field_simp [hb0]
        <;> ring
  have hdist (u v : Pt) : dist u v ^ 2 =
      (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 + (u 2 - v 2) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ, PiLp.sub_apply, add_assoc]
  let c : Fin 4 → Pt := ![0, WithLp.toLp 2 ![0,0,1],
    WithLp.toLp 2 ![b,0,1-X/2], WithLp.toLp 2 ![f,z,Y/2]]
  change IsPathConfig c X Y s
  refine ⟨?_,?_,?_,?_,?_,?_,hX,hX1,hY,hY1,hH⟩
  · unfold q; rw [hdist]
    change (0-0:ℝ)^2+(0-0)^2+(0-1)^2=1
    norm_num
  · unfold q; rw [hdist]
    change (0-b)^2+(0-0)^2+(0-(1-X/2))^2=1
    nlinarith only [hb2]
  · unfold q; rw [hdist]
    change (0-f)^2+(0-z)^2+(0-Y/2)^2=Y
    nlinarith only [hd]
  · unfold q; rw [hdist]
    change (0-b)^2+(0-0)^2+(1-(1-X/2))^2=X
    nlinarith only [hb2]
  · unfold q; rw [hdist]
    change (0-f)^2+(0-z)^2+(1-Y/2)^2=1
    nlinarith only [hd]
  · unfold q; rw [hdist]
    change (b-f)^2+(0-z)^2+(1-X/2-Y/2)^2=s
    nlinarith only [hb2,hd,hbf]

private lemma HardSphereB5.Lean.Geometry.PathCore.near_diag_positive {X Y s : ℝ} (hX : 0 < X) (hH : 0 < Hpoly X Y s)
    (hs : s < 1) (hXY : X=Y) : 0 < P4poly X Y s := by
  subst Y
  have ht : 0 < 1-s := by linarith
  have hHid : Hpoly X X s = (X*(2-X)-(1-s))*(2*X+(1-s)) := by unfold Hpoly; ring
  have hPid : P4poly X X s = (X*(2-X)-(1-s))*(X*(6-X)+3*(1-s)) := by unfold P4poly; ring
  have ha : 0 < X*(2-X)-(1-s) := by
    rw [hHid] at hH
    exact (mul_pos_iff_of_pos_right (by linarith : 0 < 2*X+(1-s))).mp hH
  rw [hPid]
  exact mul_pos ha (by nlinarith)

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1200000

private def HardSphereB5.Lean.Geometry.PathCore.halfLeft : Param → ℝ := {v : Param | v.2.1 < v.1}.indicator weight
private def HardSphereB5.Lean.Geometry.PathCore.halfRight : Param → ℝ := {v : Param | v.1 < v.2.1}.indicator weight
private lemma HardSphereB5.Lean.Geometry.PathCore.path_ae_support : ∀ᵐ v ∂pathMeasure, v ∈ support := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem support_measurable)
private lemma HardSphereB5.Lean.Geometry.PathCore.sliver_ae_off_diagonal : ∀ᵐ v ∂pathMeasure.restrict nearSliver, v.1 ≠ v.2.1 := by
  filter_upwards [ae_restrict_of_ae path_ae_support, ae_restrict_mem sliver_measurable] with v hv hs
  intro h
  exact (not_lt_of_gt (near_diag_positive hv.1 hv.2.2.2.2 hs.1 h)) hs.2

private lemma HardSphereB5.Lean.Geometry.PathCore.sliver_half_integrals :
    (∫ v in nearSliver, halfLeft v ∂pathMeasure) = (∫ v in nearSliver, weight v ∂pathMeasure)/2 ∧
    (∫ v in nearSliver, halfRight v ∂pathMeasure) = (∫ v in nearSliver, weight v ∂pathMeasure)/2 := by
  let μ := pathMeasure.restrict nearSliver
  have hcomp : halfLeft ∘ swapXY = halfRight := by
    funext v
    simp [halfLeft,halfRight,Function.comp_def,Set.indicator,weight,add_comm]
  have heq : (∫ v, halfRight v ∂μ) = ∫ v, halfLeft v ∂μ := by
    have h := swap_sliverMeasure.integral_comp swapXY.measurableEmbedding halfLeft
    change (∫ v, (halfLeft ∘ swapXY) v ∂μ) = _ at h
    rw [hcomp] at h
    exact h
  have hintiff : Integrable halfRight μ ↔ Integrable halfLeft μ := by
    have h := swap_sliverMeasure.integrable_comp_emb swapXY.measurableEmbedding (g := halfLeft)
    rw [hcomp] at h
    exact h
  have hsum : (fun v => halfLeft v + halfRight v) =ᵐ[μ] weight := by
    filter_upwards [sliver_ae_off_diagonal] with v hv
    rcases lt_or_gt_of_ne hv with h|h
    · simp [halfLeft,halfRight,Set.indicator,h,not_lt_of_gt h]
    · simp [halfLeft,halfRight,Set.indicator,h,not_lt_of_gt h]
  change (∫ v, halfLeft v ∂μ) = (∫ v, weight v ∂μ)/2 ∧
    (∫ v, halfRight v ∂μ) = (∫ v, weight v ∂μ)/2
  by_cases hw : Integrable weight μ
  · have hl : Integrable halfLeft μ := hw.indicator (by measurability)
    have hr : Integrable halfRight μ := hintiff.mpr hl
    have hh := integral_congr_ae hsum
    rw [integral_add hl hr] at hh
    constructor <;> linarith
  · have hl : ¬Integrable halfLeft μ := by
      intro h
      exact hw ((h.add (hintiff.mpr h)).congr hsum)
    have hr : ¬Integrable halfRight μ := fun h => hl (hintiff.mp h)
    rw [integral_undef hl,integral_undef hr,integral_undef hw]
    norm_num

private def HardSphereB5.Lean.Geometry.PathCore.correctionF (i j : Fin 4) (v : Param) : ℝ :=
  if isCommon (centers v) i j then weight v * g (dist (centers v i) (centers v j)) else 0
private lemma HardSphereB5.Lean.Geometry.PathCore.near_sliver_pattern (v : Param) (hv : v ∈ support) (hs : v ∈ nearSliver) :
    correctionF 0 2 v = halfLeft v * g 1 ∧ correctionF 1 3 v = halfRight v * g 1 ∧
    correctionF 0 1 v = 0 ∧ correctionF 1 2 v = 0 ∧ correctionF 0 3 v = 0 ∧ correctionF 2 3 v = 0 := by
  have hc := canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  change IsPathConfig (centers v) v.1 v.2.1 v.2.2 at hc
  have hn : v.1 ≠ v.2.1 := by
    intro h
    exact (not_lt_of_gt (near_diag_positive hv.1 hv.2.2.2.2 hs.1 h)) hs.2
  have hd02 : dist (centers v 0) (centers v 2) = 1 := by
    have h := hc.q02
    unfold q at h
    nlinarith [(dist_nonneg : 0 ≤ dist (centers v 0) (centers v 2))]
  have hd13 : dist (centers v 1) (centers v 3) = 1 := by
    have h := hc.q13
    unfold q at h
    nlinarith [(dist_nonneg : 0 ≤ dist (centers v 1) (centers v 3))]
  rcases lt_or_gt_of_ne hn with h|h
  · have ht := (sliver_table hc hs.2).2.1 hs.1 h
    simp only [Prod.mk.injEq] at ht
    rcases ht.1 with ⟨h3,h2,h1,h0⟩
    simp [correctionF,isCommon,oth1,oth2,h0,h1,h2,h3,halfLeft,halfRight,Set.indicator,h,not_lt_of_gt h,hd13]
  · have ht := (sliver_table hc hs.2).1 hs.1 h
    simp only [Prod.mk.injEq] at ht
    rcases ht.1 with ⟨h3,h2,h1,h0⟩
    simp [correctionF,isCommon,oth1,oth2,h0,h1,h2,h3,halfLeft,halfRight,Set.indicator,h,not_lt_of_gt h,hd02]

private lemma HardSphereB5.Lean.Geometry.PathCore.correction_pattern_ae : ∀ᵐ v ∂pathMeasure.restrict nearSliver,
    correctionF 0 2 v = halfLeft v * g 1 ∧ correctionF 1 3 v = halfRight v * g 1 ∧
    correctionF 0 1 v = 0 ∧ correctionF 1 2 v = 0 ∧ correctionF 0 3 v = 0 ∧ correctionF 2 3 v = 0 := by
  filter_upwards [ae_restrict_of_ae path_ae_support,ae_restrict_mem sliver_measurable] with v hv hs
  exact near_sliver_pattern v hv hs

private theorem HardSphereB5.Lean.Geometry.PathCore.equal_sliver_halves : nearCorrection 0 2=Ssliver/2 ∧ nearCorrection 1 3=Ssliver/2 ∧
  nearCorrection 0 1=0 ∧ nearCorrection 1 2=0 ∧ nearCorrection 0 3=0 ∧ nearCorrection 2 3=0 := by
  have h0 := integral_congr_ae (correction_pattern_ae.mono fun v h => h.1)
  have h1 := integral_congr_ae (correction_pattern_ae.mono fun v h => h.2.1)
  have h2 := integral_congr_ae (correction_pattern_ae.mono fun v h => h.2.2.1)
  have h3 := integral_congr_ae (correction_pattern_ae.mono fun v h => h.2.2.2.1)
  have h4 := integral_congr_ae (correction_pattern_ae.mono fun v h => h.2.2.2.2.1)
  have h5 := integral_congr_ae (correction_pattern_ae.mono fun v h => h.2.2.2.2.2)
  change (π * ∫ v in nearSliver, correctionF 0 2 v ∂pathMeasure) = Ssliver/2 ∧
    (π * ∫ v in nearSliver, correctionF 1 3 v ∂pathMeasure) = Ssliver/2 ∧
    (π * ∫ v in nearSliver, correctionF 0 1 v ∂pathMeasure) = 0 ∧
    (π * ∫ v in nearSliver, correctionF 1 2 v ∂pathMeasure) = 0 ∧
    (π * ∫ v in nearSliver, correctionF 0 3 v ∂pathMeasure) = 0 ∧
    (π * ∫ v in nearSliver, correctionF 2 3 v ∂pathMeasure) = 0
  rw [h0,h1,h2,h3,h4,h5, integral_mul_const,integral_mul_const,
    sliver_half_integrals.1,sliver_half_integrals.2]
  simp only [integral_zero,mul_zero,and_true]
  unfold Ssliver
  constructor <;> ring

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1500000

private lemma HardSphereB5.Lean.Geometry.PathCore.quadratic_roots_finite (a b c : ℝ) (ha : a ≠ 0) :
    Set.Finite {t : ℝ | a*t^2+b*t+c=0} := by
  classical
  let p : Polynomial ℝ := Polynomial.C a * Polynomial.X ^ 2 +
    Polynomial.C b * Polynomial.X + Polynomial.C c
  have hp : p ≠ 0 := by
    intro hp
    have hc := congrArg (fun q : Polynomial ℝ => q.coeff 2) hp
    apply ha
    simpa [p] using hc
  simpa [p, Polynomial.IsRoot] using Polynomial.finite_setOfPred_isRoot hp

private lemma HardSphereB5.Lean.Geometry.PathCore.p4_zero_volume : volume {v : Param | P4poly v.1 v.2.1 v.2.2=0}=0 := by
  have hS : MeasurableSet {v : Param | P4poly v.1 v.2.1 v.2.2=0} := by unfold P4poly; measurability
  have hf (x y : ℝ) : Set.Finite {z : ℝ | P4poly x y z=0} := by
    have h := quadratic_roots_finite (-3) (2*x*y+6)
      (x^2*y^2-4*x^2*y-4*x*y^2+10*x*y-3) (by norm_num)
    convert h using 1
    ext z
    simp only [Set.mem_setOf_eq]
    unfold P4poly
    ring_nf
  change ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))
    {v : Param | P4poly v.1 v.2.1 v.2.2=0}=0
  refine Measure.measure_prod_null_of_ae_null hS (Filter.Eventually.of_forall ?_)
  intro x
  refine Measure.measure_prod_null_of_ae_null
    (hS.preimage (measurable_const.prodMk measurable_id)) (Filter.Eventually.of_forall ?_)
  intro y
  exact (hf x y).measure_zero volume

private lemma HardSphereB5.Lean.Geometry.PathCore.path_ae_p4_ne : ∀ᵐ v ∂pathMeasure, P4poly v.1 v.2.1 v.2.2 ≠ 0 := by
  have hr : (volume.restrict support) {v : Param | P4poly v.1 v.2.1 v.2.2=0}=0 := by
    rw [Measure.restrict_apply (by unfold P4poly; measurability)]
    exact measure_mono_null Set.inter_subset_left p4_zero_volume
  have hh : pathMeasure {v : Param | P4poly v.1 v.2.1 v.2.2=0}=0 :=
    withDensity_absolutelyContinuous _ _ hr
  rw [ae_iff]
  simpa using hh

private def HardSphereB5.Lean.Geometry.PathCore.thetaQ (a b cc : ℝ) : ℝ := atan2 (2*√(QT a b cc)) (2*(a+b-cc)-a*b)
private def HardSphereB5.Lean.Geometry.PathCore.triangleSigma (a b cc : ℝ) : ℝ := thetaQ a b cc + thetaQ a cc b + thetaQ b cc a
private lemma HardSphereB5.Lean.Geometry.PathCore.thetaQ_swap (a b cc : ℝ) : thetaQ b a cc=thetaQ a b cc := by
  have hQ : QT b a cc=QT a b cc := by unfold QT DeltaT; ring
  have hD : 2*(b+a-cc)-b*a=2*(a+b-cc)-a*b := by ring
  unfold thetaQ
  rw [hQ,hD]
private lemma HardSphereB5.Lean.Geometry.PathCore.triangleSigma_swap12 (a b cc : ℝ) : triangleSigma b a cc=triangleSigma a b cc := by
  unfold triangleSigma
  rw [thetaQ_swap b a cc]
  ring
private lemma HardSphereB5.Lean.Geometry.PathCore.triangleSigma_swap23 (a b cc : ℝ) : triangleSigma a cc b=triangleSigma a b cc := by
  unfold triangleSigma
  rw [thetaQ_swap cc b a]
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.sigma_faces {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s) :
    sigmaF c 0=triangleSigma X 1 s ∧ sigmaF c 1=triangleSigma 1 Y s ∧
    sigmaF c 2=triangleSigma 1 Y 1 ∧ sigmaF c 3=triangleSigma 1 1 X := by
  have h01 := hc.q01; have h02 := hc.q02; have h03 := hc.q03
  have h12 := hc.q12; have h13 := hc.q13; have h23 := hc.q23
  have h10 : q c 1 0=1 := by simpa [q,dist_comm] using h01
  have h20 : q c 2 0=1 := by simpa [q,dist_comm] using h02
  have h30 : q c 3 0=Y := by simpa [q,dist_comm] using h03
  have h21 : q c 2 1=X := by simpa [q,dist_comm] using h12
  have h31 : q c 3 1=1 := by simpa [q,dist_comm] using h13
  have h32 : q c 3 2=s := by simpa [q,dist_comm] using h23
  refine ⟨?_,?_,?_,?_⟩
  · change gammaA c 1 2 3+gammaA c 2 1 3+gammaA c 3 1 2=triangleSigma X 1 s
    simp only [gammaA,Qf,triangleSigma,thetaQ,h12,h13,h23,h21,h31,h32]
  · change gammaA c 0 2 3+gammaA c 2 0 3+gammaA c 3 0 2=triangleSigma 1 Y s
    simp only [gammaA,Qf,triangleSigma,thetaQ,h02,h03,h23,h20,h30,h32]
  · change gammaA c 0 1 3+gammaA c 1 0 3+gammaA c 3 0 1=triangleSigma 1 Y 1
    simp only [gammaA,Qf,triangleSigma,thetaQ,h01,h03,h13,h10,h30,h31]
  · change gammaA c 0 1 2+gammaA c 1 0 2+gammaA c 2 0 1=triangleSigma 1 1 X
    simp only [gammaA,Qf,triangleSigma,thetaQ,h01,h02,h12,h10,h20,h21]

private lemma HardSphereB5.Lean.Geometry.PathCore.Q_faces {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s) :
    Qface c 0=QT X 1 s ∧ Qface c 1=QT 1 Y s ∧ Qface c 2=QT 1 Y 1 ∧ Qface c 3=QT 1 1 X := by
  refine ⟨?_,?_,?_,?_⟩
  · change Qf c 1 2 3=QT X 1 s
    simp only [Qf,hc.q12,hc.q13,hc.q23]
  · change Qf c 0 2 3=QT 1 Y s
    simp only [Qf,hc.q02,hc.q03,hc.q23]
  · change Qf c 0 1 3=QT 1 Y 1
    simp only [Qf,hc.q01,hc.q03,hc.q13]
  · change Qf c 0 1 2=QT 1 1 X
    simp only [Qf,hc.q01,hc.q02,hc.q12]

private lemma HardSphereB5.Lean.Geometry.PathCore.swap_face_scalars (v : Param) (hv : v∈support) :
    sigmaF (centers (swapXY v)) 0=sigmaF (centers v) 1 ∧
    sigmaF (centers (swapXY v)) 2=sigmaF (centers v) 3 ∧
    Qface (centers (swapXY v)) 0=Qface (centers v) 1 ∧
    Qface (centers (swapXY v)) 2=Qface (centers v) 3 := by
  have hc := canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  change IsPathConfig (centers v) v.1 v.2.1 v.2.2 at hc
  have hcs := canonical_config hv.2.2.1 hv.2.2.2.1 hv.1 hv.2.1
    (by rw [H_swap]; exact hv.2.2.2.2)
  change IsPathConfig (centers (swapXY v)) v.2.1 v.1 v.2.2 at hcs
  obtain ⟨hS0,hS1,hS2,hS3⟩ := sigma_faces hc
  obtain ⟨hT0,hT1,hT2,hT3⟩ := sigma_faces hcs
  obtain ⟨hQ0,hQ1,hQ2,hQ3⟩ := Q_faces hc
  obtain ⟨hR0,hR1,hR2,hR3⟩ := Q_faces hcs
  rw [hT0,hT2,hS1,hS3,hR0,hR2,hQ1,hQ3]
  refine ⟨triangleSigma_swap12 _ _ _, triangleSigma_swap23 _ _ _, ?_, ?_⟩ <;>
    unfold QT DeltaT <;> ring

private lemma HardSphereB5.Lean.Geometry.PathCore.swap_face_counts (v : Param) (hv : v∈support) (hs : v∈nearDomain)
    (hP : P4poly v.1 v.2.1 v.2.2 ≠ 0) :
    nRet (centers (swapXY v)) 0=nRet (centers v) 1 ∧
    nRet (centers (swapXY v)) 2=nRet (centers v) 3 := by
  have hc := canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  change IsPathConfig (centers v) v.1 v.2.1 v.2.2 at hc
  have hcs := canonical_config hv.2.2.1 hv.2.2.2.1 hv.1 hv.2.1
    (by rw [H_swap]; exact hv.2.2.2.2)
  change IsPathConfig (centers (swapXY v)) v.2.1 v.1 v.2.2 at hcs
  by_cases hp : 0 < P4poly v.1 v.2.1 v.2.2
  · have hp' : 0 < P4poly v.2.1 v.1 v.2.2 := by rw [P4_swap]; exact hp
    simp only [(bulk_incidence hc hp).1, (bulk_incidence hcs hp').1, and_self]
  · have hn : P4poly v.1 v.2.1 v.2.2<0 := lt_of_le_of_ne (le_of_not_gt hp) hP
    have hn' : P4poly v.2.1 v.1 v.2.2<0 := by rw [P4_swap]; exact hn
    have hxy : v.1 ≠ v.2.1 := by
      intro h
      exact (not_lt_of_gt (near_diag_positive hv.1 hv.2.2.2.2 hs h)) hn
    rcases lt_or_gt_of_ne hxy with h|h
    · have hA := (sliver_table hc hn).2.1 hs h
      have hB := (sliver_table hcs hn').1 hs h
      simp only [Prod.mk.injEq] at hA hB
      rcases hA.1 with ⟨a3,a2,a1,a0⟩
      rcases hB.1 with ⟨b3,b2,b1,b0⟩
      simp only [a3,a1,b2,b0, and_self]
    · have hA := (sliver_table hc hn).1 hs h
      have hB := (sliver_table hcs hn').2.1 hs h
      simp only [Prod.mk.injEq] at hA hB
      rcases hA.1 with ⟨a3,a2,a1,a0⟩
      rcases hB.1 with ⟨b3,b2,b1,b0⟩
      simp only [a3,a1,b2,b0, and_self]

open HardSphereB5.Lean.Geometry.PathCore
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000

private lemma HardSphereB5.Lean.Geometry.PathCore.quadratic_arcsin_deriv (a b s : ℝ) (hb : 0 < b) (hs : s∈Set.Ioo (a-b) (a+b)) :
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

private lemma HardSphereB5.Lean.Geometry.PathCore.quadratic_fiber_integrable (a b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => 1/√(b^2-(a-s)^2)) (Set.Ioo (a-b) (a+b)) := by
  have hc : Continuous (fun s : ℝ => arcsin ((s-a)/b)) := by fun_prop
  have hi := intervalIntegral.integrableOn_deriv_of_nonneg hc.continuousOn
    (fun s hs => quadratic_arcsin_deriv a b s hb hs)
    (fun s _ => one_div_nonneg.mpr (sqrt_nonneg _))
  exact hi.mono_set Set.Ioo_subset_Ioc_self

private lemma HardSphereB5.Lean.Geometry.PathCore.quadratic_fiber_integral (a b : ℝ) (hb : 0 < b) :
    (∫ s in Set.Ioo (a-b) (a+b), (1/√(b^2-(a-s)^2))) = π := by
  have hab : a-b ≤ a+b := by linarith
  have hc : Continuous (fun s : ℝ => arcsin ((s-a)/b)) := by fun_prop
  have hi := quadratic_fiber_integrable a b hb
  have hI : IntervalIntegrable (fun s : ℝ => 1/√(b^2-(a-s)^2)) volume (a-b) (a+b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr hi
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc.continuousOn
    (fun s hs => quadratic_arcsin_deriv a b s hb hs) hI
  rw [intervalIntegral.integral_of_le hab,integral_Ioc_eq_integral_Ioo] at hh
  have hm : (a-b-a)/b=(-1:ℝ) := by field_simp [hb.ne']; ring
  have hp : (a+b-a)/b=(1:ℝ) := by field_simp [hb.ne']; ring
  rw [hm,hp,arcsin_one,arcsin_neg_one] at hh
  linarith

open HardSphereB5.Lean.Geometry.PathCore
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000
private lemma HardSphereB5.Lean.Geometry.PathCore.b0_pos {X Y : ℝ} (hX : X∈Set.Ioo (0:ℝ) 1) (hY : Y∈Set.Ioo (0:ℝ) 1) : 0 < b0 X Y := by
  have hx : 0 < X*(1-X/4) := mul_pos hX.1 (by linarith [hX.2])
  have hy : 0 < Y*(1-Y/4) := mul_pos hY.1 (by linarith [hY.2])
  unfold b0 rX
  exact mul_pos (mul_pos (by norm_num) (sqrt_pos.mpr hx)) (sqrt_pos.mpr hy)

private lemma HardSphereB5.Lean.Geometry.PathCore.H_quadratic {X Y : ℝ} (hX : X∈Set.Ioo (0:ℝ) 1) (hY : Y∈Set.Ioo (0:ℝ) 1) (s : ℝ) :
    Hpoly X Y s=(b0 X Y)^2-(a0 X Y-s)^2 := by
  have hx : 0 ≤ X*(1-X/4) := mul_nonneg hX.1.le (by linarith [hX.2])
  have hy : 0 ≤ Y*(1-Y/4) := mul_nonneg hY.1.le (by linarith [hY.2])
  unfold Hpoly b0 rX a0
  rw [show (2*√(X*(1-X/4))*√(Y*(1-Y/4)))^2 = 4*(√(X*(1-X/4)))^2*(√(Y*(1-Y/4)))^2 by ring,
    Real.sq_sqrt hx,Real.sq_sqrt hy]
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.H_fiber_set {X Y : ℝ} (hX : X∈Set.Ioo (0:ℝ) 1) (hY : Y∈Set.Ioo (0:ℝ) 1) :
    {s : ℝ | 0<Hpoly X Y s}=Set.Ioo (a0 X Y-b0 X Y) (a0 X Y+b0 X Y) := by
  have hb := b0_pos hX hY
  ext s
  rw [Set.mem_setOf_eq,H_quadratic hX hY s]
  change 0<(b0 X Y)^2-(a0 X Y-s)^2 ↔ a0 X Y-b0 X Y<s ∧ s<a0 X Y+b0 X Y
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (a0 X Y-s-b0 X Y),sq_nonneg (a0 X Y-s+b0 X Y)]
  · rintro ⟨hl,hr⟩
    nlinarith

private lemma HardSphereB5.Lean.Geometry.PathCore.path_fiber_mass {X Y : ℝ} (hX : X∈Set.Ioo (0:ℝ) 1) (hY : Y∈Set.Ioo (0:ℝ) 1) :
    (∫⁻ s in {s : ℝ | 0<Hpoly X Y s}, ENNReal.ofReal (π/√(Hpoly X Y s)))=ENNReal.ofReal (π^2) := by
  rw [H_fiber_set hX hY]
  simp_rw [H_quadratic hX hY]
  have hi := (quadratic_fiber_integrable (a0 X Y) (b0 X Y) (b0_pos hX hY)).const_mul π
  have hI := quadratic_fiber_integral (a0 X Y) (b0 X Y) (b0_pos hX hY)
  have heq : (fun s : ℝ => π/√((b0 X Y)^2-(a0 X Y-s)^2)) =
      (fun s => π*(1/√((b0 X Y)^2-(a0 X Y-s)^2))) := by funext s; ring
  have hi' : IntegrableOn (fun s : ℝ => π/√((b0 X Y)^2-(a0 X Y-s)^2))
      (Set.Ioo (a0 X Y-b0 X Y) (a0 X Y+b0 X Y)) := by rw [heq]; exact hi
  rw [← ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ fun s => div_nonneg pi_pos.le (sqrt_nonneg _))]
  have hJ : (∫ s in Set.Ioo (a0 X Y-b0 X Y) (a0 X Y+b0 X Y), π/√((b0 X Y)^2-(a0 X Y-s)^2))=π^2 := by
    rw [heq,integral_const_mul,hI]
    ring
  rw [hJ]

open HardSphereB5.Lean.Geometry.PathCore
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000

private def HardSphereB5.Lean.Geometry.PathCore.fullDensity (v : Param) : ENNReal := support.indicator
  (fun v => ENNReal.ofReal (π/√(Hpoly v.1 v.2.1 v.2.2))) v
private lemma HardSphereB5.Lean.Geometry.PathCore.fullDensity_measurable : Measurable fullDensity := by
  exact (by unfold Hpoly; fun_prop : Measurable (fun v : Param => ENNReal.ofReal (π/√(Hpoly v.1 v.2.1 v.2.2)))).indicator support_measurable

private lemma HardSphereB5.Lean.Geometry.PathCore.fullDensity_fiber (X Y : ℝ) :
    (∫⁻ s : ℝ, fullDensity (X,Y,s))=
      (if X∈Set.Ioo (0:ℝ) 1 then (Set.Ioo (0:ℝ) 1).indicator (fun _ => ENNReal.ofReal (π^2)) Y else 0) := by
  by_cases hX : X∈Set.Ioo (0:ℝ) 1
  · rw [if_pos hX]
    by_cases hY : Y∈Set.Ioo (0:ℝ) 1
    · rw [Set.indicator_of_mem hY]
      have heq (s : ℝ) : fullDensity (X,Y,s)=
          {s : ℝ | 0<Hpoly X Y s}.indicator (fun s => ENNReal.ofReal (π/√(Hpoly X Y s))) s := by
        simp [fullDensity,support,Set.indicator,hX.1,hX.2,hY.1,hY.2]
      simp_rw [heq]
      rw [lintegral_indicator (by unfold Hpoly; measurability)]
      exact path_fiber_mass hX hY
    · rw [Set.indicator_of_notMem hY]
      have heq (s : ℝ) : fullDensity (X,Y,s)=0 := by
        apply Set.indicator_of_notMem
        exact fun h => hY ⟨h.2.2.1,h.2.2.2.1⟩
      simp_rw [heq]
      simp
  · rw [if_neg hX]
    have heq (s : ℝ) : fullDensity (X,Y,s)=0 := by
      apply Set.indicator_of_notMem
      exact fun h => hX ⟨h.1,h.2.1⟩
    simp_rw [heq]
    simp

private lemma HardSphereB5.Lean.Geometry.PathCore.pathMeasure_total_mass : pathMeasure Set.univ=ENNReal.ofReal (π^2) := by
  unfold pathMeasure
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,←lintegral_indicator support_measurable]
  change (∫⁻ v : Param, fullDensity v)=ENNReal.ofReal (π^2)
  rw [show (volume : Measure Param)=(volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)) from rfl]
  rw [lintegral_prod _ fullDensity_measurable.aemeasurable]
  have hf (X : ℝ) : (∫⁻ p : ℝ×ℝ, fullDensity (X,p))=
      (Set.Ioo (0:ℝ) 1).indicator (fun _ => ENNReal.ofReal (π^2)) X := by
    rw [show (volume : Measure (ℝ×ℝ))=(volume : Measure ℝ).prod (volume : Measure ℝ) from rfl]
    rw [lintegral_prod (fun p : ℝ×ℝ => fullDensity (X,p)) (fullDensity_measurable.comp (measurable_const.prodMk measurable_id)).aemeasurable]
    simp_rw [fullDensity_fiber]
    by_cases hx : X∈Set.Ioo (0:ℝ) 1
    · simp only [if_pos hx,Set.indicator_of_mem hx]
      rw [lintegral_indicator measurableSet_Ioo]
      simp
    · simp [hx,Set.indicator]
  change (∫⁻ X : ℝ, (∫⁻ p : ℝ×ℝ, fullDensity (X,p)))=ENNReal.ofReal (π^2)
  calc
    _ = ∫⁻ X : ℝ, (Set.Ioo (0:ℝ) 1).indicator (fun _ => ENNReal.ofReal (π^2)) X := lintegral_congr hf
    _ = ENNReal.ofReal (π^2) := by rw [lintegral_indicator measurableSet_Ioo]; simp

private lemma HardSphereB5.Lean.Geometry.PathCore.pathMeasure_finite : IsFiniteMeasure pathMeasure := by
  constructor
  rw [pathMeasure_total_mass]
  exact ENNReal.ofReal_lt_top
private lemma HardSphereB5.Lean.Geometry.PathCore.nearMeasure_finite : IsFiniteMeasure (pathMeasure.restrict nearDomain) := by
  letI := pathMeasure_finite
  infer_instance

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000

private def HardSphereB5.Lean.Geometry.PathCore.countSelector (l : Fin 4) (v : Param) : ℝ :=
  if 0<P4poly v.1 v.2.1 v.2.2 then 1 else if 0<Qpoly v.1 v.2.1 v.2.2 l ∧ Apoly v.1 v.2.1 v.2.2 l<0 then 2 else 0
private lemma HardSphereB5.Lean.Geometry.PathCore.countSelector_measurable (l : Fin 4) : Measurable (countSelector l) := by
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
    fin_cases l
    · change Measurable (fun v : Param => -v.1^2+v.1*v.2.2+2*v.1-v.2.2^2+2*v.2.2-1)
      fun_prop
    · change Measurable (fun v : Param => -v.2.1^2+v.2.1*v.2.2+2*v.2.1-v.2.2^2+2*v.2.2-1)
      fun_prop
    · change Measurable (fun v : Param => v.2.1*(3-v.2.1))
      fun_prop
    · change Measurable (fun v : Param => v.1*(3-v.1))
      fun_prop
  have hQ : MeasurableSet {v : Param | 0<Qpoly v.1 v.2.1 v.2.2 l} := measurableSet_lt measurable_const hQ'
  exact measurable_const.ite hP (measurable_const.ite (hQ.inter hA) measurable_const)
private lemma HardSphereB5.Lean.Geometry.PathCore.count_ae (l : Fin 4) : ∀ᵐ v ∂pathMeasure,
    (nRet (centers v) l : ℝ)=countSelector l v := by
  filter_upwards [path_ae_support,path_ae_p4_ne] with v hv hp
  have hc := canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  change IsPathConfig (centers v) v.1 v.2.1 v.2.2 at hc
  unfold countSelector
  by_cases hb : 0<P4poly v.1 v.2.1 v.2.2
  · rw [(bulk_incidence hc hb).1 l,if_pos hb]
    norm_num
  · have hs : P4poly v.1 v.2.1 v.2.2<0 := lt_of_le_of_ne (le_of_not_gt hb) hp
    rw [(sliver_incidence hc hs).1 l,if_neg hb]
    split_ifs <;> norm_num
private lemma HardSphereB5.Lean.Geometry.PathCore.count_integrable (l : Fin 4) : Integrable (fun v => (nRet (centers v) l : ℝ)) pathMeasure := by
  letI := pathMeasure_finite
  have hi : Integrable (countSelector l) pathMeasure := by
    refine (integrable_const (2:ℝ)).mono' (countSelector_measurable l).aestronglyMeasurable
      (ae_of_all _ fun v => ?_)
    unfold countSelector
    split_ifs <;> norm_num
  exact hi.congr ((count_ae l).mono fun v h => h.symm)
private lemma HardSphereB5.Lean.Geometry.PathCore.weight_integrable : Integrable weight pathMeasure := by
  letI := pathMeasure_finite
  refine (integrable_const (1:ℝ)).mono' (by unfold weight; fun_prop)
    (path_ae_support.mono fun v hv => ?_)
  unfold weight
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [hv.1,hv.2.2.1])]
  linarith [hv.2.1,hv.2.2.2.1]
private lemma HardSphereB5.Lean.Geometry.PathCore.centers_measurable : Measurable centers := by
  unfold centers canonicalCenters rX a0 Hpoly
  fun_prop
private lemma HardSphereB5.Lean.Geometry.PathCore.beta_measurable (i j k : Fin 4) : Measurable (fun v => betaA (centers v) i j k) := by
  have hc (l : Fin 4) : Measurable (fun v => centers v l) := (measurable_pi_apply l).comp centers_measurable
  have hci := hc i; have hcj := hc j; have hck := hc k
  unfold betaA atan2 Qf QT DeltaT q
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop
private lemma HardSphereB5.Lean.Geometry.PathCore.phi_measurable (i j : Fin 4) : Measurable (fun v => phiE (centers v) i j) := by
  have hc (l : Fin 4) : Measurable (fun v => centers v l) := (measurable_pi_apply l).comp centers_measurable
  have hci := hc i; have hcj := hc j; have hck := hc (oth1 i j); have hcl := hc (oth2 i j)
  unfold phiE dihedral InnerProductGeometry.angle perpProj
  fun_prop
private lemma HardSphereB5.Lean.Geometry.PathCore.beta_integrable (i j k : Fin 4) : Integrable (fun v => betaA (centers v) i j k) pathMeasure := by
  letI := pathMeasure_finite
  refine (integrable_const π).mono' (beta_measurable i j k).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  exact Complex.abs_arg_le_pi _
private lemma HardSphereB5.Lean.Geometry.PathCore.phi_integrable (i j : Fin 4) : Integrable (fun v => phiE (centers v) i j) pathMeasure := by
  letI := pathMeasure_finite
  refine (integrable_const π).mono' (phi_measurable i j).aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  unfold phiE dihedral
  rw [Real.norm_eq_abs,abs_of_nonneg (InnerProductGeometry.angle_nonneg _ _)]
  exact InnerProductGeometry.angle_le_pi _ _

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000
private lemma HardSphereB5.Lean.Geometry.PathCore.weight_bound (v : Param) (hv : v∈support) : ‖weight v‖≤1 := by
  unfold weight
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [hv.1,hv.2.2.1])]
  linarith [hv.2.1,hv.2.2.2.1]
private lemma HardSphereB5.Lean.Geometry.PathCore.count_bound_ae (l : Fin 4) : ∀ᵐ v ∂pathMeasure, ‖(nRet (centers v) l : ℝ)‖≤2 := by
  filter_upwards [count_ae l] with v hv
  rw [hv]
  unfold countSelector
  split_ifs <;> norm_num
private lemma HardSphereB5.Lean.Geometry.PathCore.near_dist_bound (v : Param) (hv : v∈support) (hs : v∈nearDomain) (i j : Fin 4) :
    dist (centers v i) (centers v j)≤1 := by
  have hc := canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
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
private lemma HardSphereB5.Lean.Geometry.PathCore.g_bound {d : ℝ} (hd0 : 0≤d) (hd1 : d≤1) : ‖g d‖≤2 := by
  have h3 : 0≤d^3 := pow_nonneg hd0 _
  have h31 : d^3≤1 := pow_le_one₀ hd0 hd1
  rw [Real.norm_eq_abs]
  unfold g
  exact abs_le.mpr ⟨by linarith,by linarith⟩
private lemma HardSphereB5.Lean.Geometry.PathCore.g_measurable (i j : Fin 4) : Measurable (fun v => g (dist (centers v i) (centers v j))) := by
  have hi := (measurable_pi_apply i).comp centers_measurable
  have hj := (measurable_pi_apply j).comp centers_measurable
  unfold g
  fun_prop
private lemma HardSphereB5.Lean.Geometry.PathCore.g_near_bound_ae (i j : Fin 4) : ∀ᵐ v ∂pathMeasure.restrict nearDomain,
    ‖g (dist (centers v i) (centers v j))‖≤2 := by
  filter_upwards [ae_restrict_of_ae path_ae_support,ae_restrict_mem near_measurable] with v hv hs
  exact g_bound dist_nonneg (near_dist_bound v hv hs i j)
private lemma HardSphereB5.Lean.Geometry.PathCore.weighted_triangle_integrable (i j k l : Fin 4) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*(nRet (centers v) l : ℝ)*betaA (centers v) i j k)
      nearDomain pathMeasure := by
  have hb : IntegrableOn (fun v => betaA (centers v) i j k) nearDomain pathMeasure := (beta_integrable i j k).restrict
  have hc : IntegrableOn (fun v => (nRet (centers v) l : ℝ)) nearDomain pathMeasure := (count_integrable l).restrict
  have hB := hb.bdd_mul hc.aestronglyMeasurable (ae_restrict_of_ae (count_bound_ae l))
  have hG := hB.bdd_mul (g_measurable i j).aestronglyMeasurable (g_near_bound_ae i j)
  have hW : AEStronglyMeasurable weight (pathMeasure.restrict nearDomain) := weight_integrable.restrict.aestronglyMeasurable
  have h := hG.bdd_mul hW ((ae_restrict_of_ae path_ae_support).mono fun v hv => weight_bound v hv)
  simpa only [IntegrableOn,mul_assoc] using h
private lemma HardSphereB5.Lean.Geometry.PathCore.weighted_phi_integrable (i j : Fin 4) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*phiE (centers v) i j)
      nearDomain pathMeasure := by
  have hp : IntegrableOn (fun v => phiE (centers v) i j) nearDomain pathMeasure := (phi_integrable i j).restrict
  have hG := hp.bdd_mul (g_measurable i j).aestronglyMeasurable (g_near_bound_ae i j)
  have h := hG.bdd_mul weight_integrable.restrict.aestronglyMeasurable
    ((ae_restrict_of_ae path_ae_support).mono fun v hv => weight_bound v hv)
  simpa only [IntegrableOn,mul_assoc] using h
private lemma HardSphereB5.Lean.Geometry.PathCore.weighted_bulk_integrable (i j : Fin 4) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*phiE (centers v) i j)
      nearBulk pathMeasure :=
  (weighted_phi_integrable i j).mono_set (fun _ hv => hv.1)

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
set_option maxHeartbeats 1800000

private def HardSphereB5.Lean.Geometry.PathCore.commonSelector (i j : Fin 4) (v : Param) : Prop :=
  countSelector (oth1 i j) v≠0 ∧ countSelector (oth2 i j) v≠0
private lemma HardSphereB5.Lean.Geometry.PathCore.commonSelector_measurable (i j : Fin 4) : MeasurableSet {v : Param | commonSelector i j v} :=
  ((measurableSet_eq_fun (countSelector_measurable (oth1 i j)) measurable_const).compl).inter
    (measurableSet_eq_fun (countSelector_measurable (oth2 i j)) measurable_const).compl
private lemma HardSphereB5.Lean.Geometry.PathCore.common_ae (i j : Fin 4) : ∀ᵐ v ∂pathMeasure,
    isCommon (centers v) i j ↔ commonSelector i j v := by
  filter_upwards [count_ae (oth1 i j),count_ae (oth2 i j)] with v h1 h2
  unfold isCommon commonSelector
  rw [←h1,←h2]
  norm_cast
private lemma HardSphereB5.Lean.Geometry.PathCore.correction_angle_integrable (i j : Fin 4) :
    Integrable (fun v => if P4poly v.1 v.2.1 v.2.2<0 ∧ isCommon (centers v) i j then 2*π else 0) pathMeasure := by
  letI := pathMeasure_finite
  let t : Set Param := {v | P4poly v.1 v.2.1 v.2.2<0 ∧ commonSelector i j v}
  have hP : MeasurableSet {v : Param | P4poly v.1 v.2.1 v.2.2<0} := by unfold P4poly; measurability
  have ht : MeasurableSet t := hP.inter (commonSelector_measurable i j)
  have hi : Integrable (t.indicator (fun _ : Param => 2*π)) pathMeasure := (integrable_const (2*π)).indicator ht
  refine hi.congr ?_
  filter_upwards [common_ae i j] with v hv
  simp only [t,Set.indicator,Set.mem_setOf_eq,hv]
private lemma HardSphereB5.Lean.Geometry.PathCore.weighted_correction_integrable (i j : Fin 4) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if P4poly v.1 v.2.1 v.2.2<0 ∧ isCommon (centers v) i j then 2*π else 0)) nearDomain pathMeasure := by
  have hc : Integrable (fun v => if P4poly v.1 v.2.1 v.2.2<0 ∧ isCommon (centers v) i j then 2*π else 0)
      (pathMeasure.restrict nearDomain) := (correction_angle_integrable i j).restrict
  have hG := hc.bdd_mul (g_measurable i j).aestronglyMeasurable (g_near_bound_ae i j)
  have h := hG.bdd_mul weight_integrable.restrict.aestronglyMeasurable
    ((ae_restrict_of_ae path_ae_support).mono fun v hv => weight_bound v hv)
  simpa only [IntegrableOn,mul_assoc] using h
private lemma HardSphereB5.Lean.Geometry.PathCore.conditional_phi_integrable (i j : Fin 4) :
    IntegrableOn (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if 0<P4poly v.1 v.2.1 v.2.2 then phiE (centers v) i j else 0)) nearDomain pathMeasure := by
  have hP : MeasurableSet {v : Param | 0<P4poly v.1 v.2.1 v.2.2} := by unfold P4poly; measurability
  have hf : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*phiE (centers v) i j)
      (pathMeasure.restrict nearDomain) := weighted_phi_integrable i j
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

private theorem HardSphereB5.Lean.Geometry.PathCore.pair_arc_integrable_of_pair_width
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
    weighted_triangle_integrable i j (oth1 i j) (oth2 i j)
  have hB : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*
      (nRet (centers v) (oth1 i j) : ℝ)*betaA (centers v) i j (oth2 i j)) μ :=
    weighted_triangle_integrable i j (oth2 i j) (oth1 i j)
  have hP : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if 0<P4poly v.1 v.2.1 v.2.2 then phiE (centers v) i j else 0)) μ := conditional_phi_integrable i j
  have hC : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if P4poly v.1 v.2.1 v.2.2<0 ∧ isCommon (centers v) i j then 2*π else 0)) μ := weighted_correction_integrable i j
  change Integrable _ μ
  refine (((hA.add hB).sub hP).sub hC).congr ?_
  filter_upwards [ae_restrict_of_ae path_ae_support,ae_restrict_of_ae path_ae_p4_ne] with v hv hp
  have hc := canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  change IsPathConfig (centers v) v.1 v.2.1 v.2.2 at hc
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [hWidth hc hp i j hij]
  ring

open HardSphereB5.Lean.Geometry.PathCore
open MeasureTheory Real
open HardSphereB5.Lean (Pt)
open scoped Classical
set_option maxHeartbeats 2000000

@[simp] private lemma s4b_q_self (c : Fin 4 → Pt) (i : Fin 4) : q c i i = 0 := by simp [q]

private def HardSphereB5.Lean.Geometry.PathCore.s4b_label : Fin 4 → Fin 4 := ![1,0,3,2]
@[simp] private lemma s4b_label0 : s4b_label 0=1 := rfl
@[simp] private lemma s4b_label1 : s4b_label 1=0 := rfl
@[simp] private lemma s4b_label2 : s4b_label 2=3 := rfl
@[simp] private lemma s4b_label3 : s4b_label 3=2 := rfl

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_q_swap (v : Param) (hv : v ∈ support) :
    ∀ i j, q (centers (swapXY v)) i j = q (centers v) (s4b_label i) (s4b_label j) := by
  have hc := canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  change IsPathConfig (centers v) v.1 v.2.1 v.2.2 at hc
  have hd := canonical_config hv.2.2.1 hv.2.2.2.1 hv.1 hv.2.1
    (by rw [H_swap]; exact hv.2.2.2.2)
  change IsPathConfig (centers (swapXY v)) v.2.1 v.1 v.2.2 at hd
  have hc10 : q (centers v) 1 0=1 := by rw [q_symm',hc.q01]
  have hc20 : q (centers v) 2 0=1 := by rw [q_symm',hc.q02]
  have hc30 : q (centers v) 3 0=v.2.1 := by rw [q_symm',hc.q03]
  have hc21 : q (centers v) 2 1=v.1 := by rw [q_symm',hc.q12]
  have hc31 : q (centers v) 3 1=1 := by rw [q_symm',hc.q13]
  have hc32 : q (centers v) 3 2=v.2.2 := by rw [q_symm',hc.q23]
  have hd10 : q (centers (swapXY v)) 1 0=1 := by rw [q_symm',hd.q01]
  have hd20 : q (centers (swapXY v)) 2 0=1 := by rw [q_symm',hd.q02]
  have hd30 : q (centers (swapXY v)) 3 0=v.1 := by rw [q_symm',hd.q03]
  have hd21 : q (centers (swapXY v)) 2 1=v.2.1 := by rw [q_symm',hd.q12]
  have hd31 : q (centers (swapXY v)) 3 1=1 := by rw [q_symm',hd.q13]
  have hd32 : q (centers (swapXY v)) 3 2=v.2.2 := by rw [q_symm',hd.q23]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.reduceFinMk,s4b_label0,s4b_label1,s4b_label2,s4b_label3,s4b_q_self,hc.q01,hc.q02,hc.q03,hc.q12,hc.q13,hc.q23,
      hd.q01,hd.q02,hd.q03,hd.q12,hd.q13,hd.q23,
      hc10,hc20,hc30,hc21,hc31,hc32,hd10,hd20,hd30,hd21,hd31,hd32]
  all_goals clear hv hc hd hc10 hc20 hc30 hc21 hc31 hc32 hd10 hd20 hd30 hd21 hd31 hd32

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_dist_q_congr {c d : Fin 4 → Pt} (h : ∀ i j, q c i j=q d i j) (i j : Fin 4) :
    dist (c i) (c j)=dist (d i) (d j) := by
  have hh := h i j
  unfold q at hh
  nlinarith [(dist_nonneg : 0 ≤ dist (c i) (c j)),(dist_nonneg : 0 ≤ dist (d i) (d j))]

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_beta_q_congr {c d : Fin 4 → Pt} (h : ∀ i j, q c i j=q d i j) (i j k : Fin 4) :
    betaA c i j k=betaA d i j k := by simp only [betaA,Qf,h]

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_perp_inner (v w z : Pt) :
    inner ℝ (perpProj v w) (perpProj v z) =
      inner ℝ w z - (inner ℝ z v / inner ℝ v v)*inner ℝ w v
      - (inner ℝ w v / inner ℝ v v)*inner ℝ v z
      + (inner ℝ w v / inner ℝ v v)*(inner ℝ z v / inner ℝ v v)*inner ℝ v v := by
  simp only [perpProj,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_proj_inner_q_congr {c d : Fin 4 → Pt} (h : ∀ i j, q c i j=q d i j)
    (i j k l : Fin 4) :
    inner ℝ (perpProj (c j-c i) (c k-c i)) (perpProj (c j-c i) (c l-c i)) =
      inner ℝ (perpProj (d j-d i) (d k-d i)) (perpProj (d j-d i) (d l-d i)) := by
  simp only [s4b_perp_inner,inner_from_q,h]

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_dihedral_q_congr {c d : Fin 4 → Pt} (h : ∀ i j, q c i j=q d i j)
    (i j k l : Fin 4) : dihedral c i j k l=dihedral d i j k l := by
  have hn (a : Fin 4) : ‖perpProj (c j-c i) (c a-c i)‖ =
      ‖perpProj (d j-d i) (d a-d i)‖ := by
    rw [norm_eq_sqrt_real_inner,norm_eq_sqrt_real_inner,s4b_proj_inner_q_congr h]
  simp only [dihedral,InnerProductGeometry.angle,s4b_proj_inner_q_congr h,hn]

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_dist_swap (v : Param) (hv : v∈support) (i j : Fin 4) :
    dist (centers (swapXY v) i) (centers (swapXY v) j)=
      dist (centers v (s4b_label i)) (centers v (s4b_label j)) := by
  exact s4b_dist_q_congr (c := centers (swapXY v))
    (d := fun a => centers v (s4b_label a)) (s4b_q_swap v hv) i j

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_beta_swap (v : Param) (hv : v∈support) (i j k : Fin 4) :
    betaA (centers (swapXY v)) i j k=
      betaA (centers v) (s4b_label i) (s4b_label j) (s4b_label k) := by
  exact s4b_beta_q_congr (c := centers (swapXY v))
    (d := fun a => centers v (s4b_label a)) (s4b_q_swap v hv) i j k

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_phi_swap (v : Param) (hv : v∈support) :
    phiE (centers (swapXY v)) 0 2=phiE (centers v) 1 3 ∧
    phiE (centers (swapXY v)) 0 3=phiE (centers v) 1 2 := by
  have h:=s4b_q_swap v hv
  have ha:=s4b_dihedral_q_congr (c := centers (swapXY v))
    (d := fun a => centers v (s4b_label a)) h 0 2 1 3
  have hb:=s4b_dihedral_q_congr (c := centers (swapXY v))
    (d := fun a => centers v (s4b_label a)) h 0 3 1 2
  constructor
  · simpa [phiE,oth1,oth2,dihedral,s4b_label] using ha
  · simpa [phiE,oth1,oth2,dihedral,s4b_label] using hb

open HardSphereB5.Lean.Geometry.PathCore
open MeasureTheory Real
open HardSphereB5.Lean (Pt)
open scoped Classical
set_option maxHeartbeats 2000000

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_beta_pair_symm (c : Fin 4 → Pt) (i j k : Fin 4) :
    betaA c j i k=betaA c i j k := by
  have hQ : Qf c j i k=Qf c i j k := by
    simp only [Qf,QT,DeltaT,q_symm' c j i]
    ring
  simp only [betaA,hQ,q_symm' c j i]
  congr 1
  ring

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_counts_swap (v : Param) (hv : v∈support) (hs : v∈nearDomain)
    (hp : P4poly v.1 v.2.1 v.2.2≠0) :
    ∀ l, nRet (centers (swapXY v)) l=nRet (centers v) (s4b_label l) := by
  have h:=swap_face_counts v hv hs hp
  have hv' : swapXY v∈support := by
    change v∈swapXY ⁻¹' support
    rw [swap_support]
    exact hv
  have hs' : swapXY v∈nearDomain := hs
  have hp' : P4poly (swapXY v).1 (swapXY v).2.1 (swapXY v).2.2≠0 := by
    simpa only [swapXY_apply,P4_swap] using hp
  have h':=swap_face_counts (swapXY v) hv' hs' hp'
  simp only [swapXY_twice] at h'
  intro l
  fin_cases l <;> simp only [Fin.reduceFinMk,s4b_label0,s4b_label1,s4b_label2,s4b_label3]
  · exact h.1
  · exact h'.1.symm
  · exact h.2
  · exact h'.2.symm

private def HardSphereB5.Lean.Geometry.PathCore.s4b_triangleDensity (i j k l : Fin 4) (v : Param) : ℝ :=
  weight v * g (dist (centers v i) (centers v j)) * (nRet (centers v) l : ℝ) *
    betaA (centers v) i j k

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_triangle_density_swap (v : Param) (hv : v∈support) (hs : v∈nearDomain)
    (hp : P4poly v.1 v.2.1 v.2.2≠0) (i j k l : Fin 4) :
    s4b_triangleDensity i j k l (swapXY v)=
      s4b_triangleDensity (s4b_label i) (s4b_label j) (s4b_label k) (s4b_label l) v := by
  simp only [s4b_triangleDensity,weight_swap,s4b_dist_swap v hv i j,
    s4b_counts_swap v hv hs hp l,s4b_beta_swap v hv i j k]

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_triangle_transport (i j k l : Fin 4) :
    triangleSide i j k l=
      triangleSide (s4b_label i) (s4b_label j) (s4b_label k) (s4b_label l) := by
  have ha : (fun v => s4b_triangleDensity i j k l (swapXY v)) =ᵐ[pathMeasure.restrict nearDomain]
      (fun v => s4b_triangleDensity (s4b_label i) (s4b_label j) (s4b_label k) (s4b_label l) v) := by
    filter_upwards [ae_restrict_of_ae path_ae_support,ae_restrict_of_ae path_ae_p4_ne,
      ae_restrict_mem near_measurable] with v hv hp hs
    exact s4b_triangle_density_swap v hv hs hp i j k l
  have ht:=swap_nearMeasure.integral_comp swapXY.measurableEmbedding (s4b_triangleDensity i j k l)
  change (-1/2:ℝ)*(∫ v in nearDomain, s4b_triangleDensity i j k l v ∂pathMeasure)=
    (-1/2:ℝ)*(∫ v in nearDomain,
      s4b_triangleDensity (s4b_label i) (s4b_label j) (s4b_label k) (s4b_label l) v ∂pathMeasure)
  exact congrArg (fun z : ℝ => (-1/2)*z) (ht.symm.trans (integral_congr_ae ha))

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_triangle_pair_symm (i j k l : Fin 4) : triangleSide j i k l=triangleSide i j k l := by
  unfold triangleSide
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  rw [dist_comm (centers v j) (centers v i),s4b_beta_pair_symm]

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_dist_eq_of_q_eq (c : Fin 4 → Pt) (i j k l : Fin 4) (h : q c i j=q c k l) :
    dist (c i) (c j)=dist (c k) (c l) := by
  unfold q at h
  nlinarith [(dist_nonneg : 0≤dist (c i) (c j)),(dist_nonneg : 0≤dist (c k) (c l))]

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_adjacent_unit_density_ae : ∀ᵐ v ∂pathMeasure.restrict nearDomain,
    s4b_triangleDensity 0 2 1 3 v=s4b_triangleDensity 0 1 2 3 v ∧
    s4b_triangleDensity 1 3 0 2 v=s4b_triangleDensity 0 1 3 2 v := by
  filter_upwards [ae_restrict_of_ae path_ae_support] with v hv
  have hc:=canonical_config hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  change IsPathConfig (centers v) v.1 v.2.1 v.2.2 at hc
  have h02:=s4b_dist_eq_of_q_eq (centers v) 0 2 0 1 (hc.q02.trans hc.q01.symm)
  have h13:=s4b_dist_eq_of_q_eq (centers v) 1 3 0 1 (hc.q13.trans hc.q01.symm)
  have hb:=adjacent_unit_halfwidths hc
  simp only [s4b_triangleDensity,h02,h13,hb.1.symm,hb.2.symm,and_self]

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_adjacent_unit_sides :
    triangleSide 0 2 1 3=triangleSide 0 1 2 3 ∧ triangleSide 1 3 0 2=triangleSide 0 1 3 2 := by
  have h0:=integral_congr_ae (s4b_adjacent_unit_density_ae.mono fun v h => h.1)
  have h1:=integral_congr_ae (s4b_adjacent_unit_density_ae.mono fun v h => h.2)
  constructor
  · exact congrArg (fun z : ℝ => (-1/2)*z) h0
  · exact congrArg (fun z : ℝ => (-1/2)*z) h1

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_swap_bulk : swapXY ⁻¹' nearBulk=nearBulk := by
  ext v
  simp only [Set.mem_preimage,nearBulk,Set.mem_setOf_eq,swapXY_apply,P4_swap]
private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_bulk_measurable : MeasurableSet nearBulk := by unfold nearBulk P4poly; measurability
private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_swap_bulkMeasure : MeasurePreserving swapXY (pathMeasure.restrict nearBulk)
    (pathMeasure.restrict nearBulk) := by
  simpa only [s4b_swap_bulk] using swap_pathMeasure.restrict_preimage s4b_bulk_measurable

private def HardSphereB5.Lean.Geometry.PathCore.s4b_bulkDensity (i j : Fin 4) (v : Param) : ℝ :=
  weight v * g (dist (centers v i) (centers v j)) * phiE (centers v) i j

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_bulk_density_ae : ∀ᵐ v ∂pathMeasure.restrict nearBulk,
    s4b_bulkDensity 0 2 (swapXY v)=s4b_bulkDensity 1 3 v ∧
    s4b_bulkDensity 0 3 (swapXY v)=s4b_bulkDensity 1 2 v := by
  filter_upwards [ae_restrict_of_ae path_ae_support] with v hv
  have h02:=s4b_dist_swap v hv 0 2
  have h03:=s4b_dist_swap v hv 0 3
  simp only [s4b_label0,s4b_label2,s4b_label3] at h02 h03
  have hp:=s4b_phi_swap v hv
  simp only [s4b_bulkDensity,weight_swap,h02,h03,hp.1,hp.2,and_self]

private lemma HardSphereB5.Lean.Geometry.PathCore.s4b_bulk_pairs : bulkSource 1 3=bulkSource 0 2 ∧ bulkSource 0 3=bulkSource 1 2 := by
  have h02:=s4b_swap_bulkMeasure.integral_comp swapXY.measurableEmbedding (s4b_bulkDensity 0 2)
  have h03:=s4b_swap_bulkMeasure.integral_comp swapXY.measurableEmbedding (s4b_bulkDensity 0 3)
  have c02:=integral_congr_ae (s4b_bulk_density_ae.mono fun v h => h.1)
  have c03:=integral_congr_ae (s4b_bulk_density_ae.mono fun v h => h.2)
  constructor
  · exact (congrArg (fun z : ℝ => (1/2)*z) (h02.symm.trans c02)).symm
  · exact congrArg (fun z : ℝ => (1/2)*z) (h03.symm.trans c03)

private theorem HardSphereB5.Lean.Geometry.PathCore.s4_arc_label_transport :
    triangleSide 0 1 3 2=triangleSide 0 1 2 3 ∧
    triangleSide 0 2 1 3=triangleSide 0 1 2 3 ∧
    triangleSide 1 3 0 2=triangleSide 0 1 2 3 ∧
    triangleSide 0 3 1 2=triangleSide 1 2 0 3 ∧
    triangleSide 1 3 2 0=triangleSide 0 2 3 1 ∧
    triangleSide 1 2 3 0=triangleSide 0 3 2 1 ∧
    triangleSide 2 3 1 0=triangleSide 2 3 0 1 ∧
    bulkSource 1 3=bulkSource 0 2 ∧ bulkSource 0 3=bulkSource 1 2 := by
  have h1 : triangleSide 0 1 3 2=triangleSide 0 1 2 3 := by
    have h:=s4b_triangle_transport 0 1 2 3
    simp only [s4b_label0,s4b_label1,s4b_label2,s4b_label3] at h
    exact (h.trans (s4b_triangle_pair_symm 0 1 3 2)).symm
  have h4:=s4b_triangle_transport 0 3 1 2
  have h5:=(s4b_triangle_transport 0 2 3 1).symm
  have h6:=(s4b_triangle_transport 0 3 2 1).symm
  have h7:=s4b_triangle_transport 2 3 0 1
  simp only [s4b_label0,s4b_label1,s4b_label2,s4b_label3] at h4 h5 h6 h7
  have h7' : triangleSide 2 3 1 0=triangleSide 2 3 0 1 :=
    (h7.trans (s4b_triangle_pair_symm 2 3 1 0)).symm
  exact ⟨h1,s4b_adjacent_unit_sides.1,s4b_adjacent_unit_sides.2.trans h1,
    h4,h5,h6,h7',s4b_bulk_pairs.1,s4b_bulk_pairs.2⟩

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
private def HardSphereB5.Lean.Geometry.PathCore.S4PairWidthSignature : Prop := ∀ {c : Fin 4 → Pt} {X Y s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (i j : Fin 4) (hij : i ≠ j),
    ell c i j = (nRet c (oth2 i j) : ℝ) * betaA c i j (oth1 i j)
        + (nRet c (oth1 i j) : ℝ) * betaA c i j (oth2 i j)
        - (if 0 < P4poly X Y s then phiE c i j else 0)
        - (if P4poly X Y s < 0 ∧ isCommon c i j then 2 * π else 0)

private def HardSphereB5.Lean.Geometry.PathCore.s4FaceArc (i j k : Fin 4) (l : Fin 4) (v : Param) : ℝ :=
  weight v*g (dist (centers v i) (centers v j))*(nRet (centers v) l : ℝ)*betaA (centers v) i j k

private def HardSphereB5.Lean.Geometry.PathCore.s4BulkArc (i j : Fin 4) (v : Param) : ℝ :=
  if 0<P4poly v.1 v.2.1 v.2.2 then weight v*g (dist (centers v i) (centers v j))*phiE (centers v) i j else 0

private def HardSphereB5.Lean.Geometry.PathCore.s4CorrectionArc (i j : Fin 4) (v : Param) : ℝ :=
  if P4poly v.1 v.2.1 v.2.2<0 then
    (if isCommon (centers v) i j then weight v*g (dist (centers v i) (centers v j)) else 0) else 0

private lemma HardSphereB5.Lean.Geometry.PathCore.s4_bulk_integral (i j : Fin 4) :
  (1/2:ℝ)*(∫ v in nearDomain, s4BulkArc i j v ∂pathMeasure)=bulkSource i j := by
  unfold s4BulkArc bulkSource
  have hm : MeasurableSet {v : Param | 0<P4poly v.1 v.2.1 v.2.2} := by unfold P4poly;measurability
  have he : (fun v : Param => if 0<P4poly v.1 v.2.1 v.2.2 then
      weight v*g (dist (centers v i) (centers v j))*phiE (centers v) i j else 0)=
      {v : Param | 0<P4poly v.1 v.2.1 v.2.2}.indicator
        (fun v => weight v*g (dist (centers v i) (centers v j))*phiE (centers v) i j) := rfl
  rw [he, setIntegral_indicator hm]
  rfl

private lemma HardSphereB5.Lean.Geometry.PathCore.s4_correction_integral (i j : Fin 4) :
  π*(∫ v in nearDomain, s4CorrectionArc i j v ∂pathMeasure)=nearCorrection i j := by
  unfold s4CorrectionArc nearCorrection
  have hm : MeasurableSet {v : Param | P4poly v.1 v.2.1 v.2.2<0} := by unfold P4poly;measurability
  change π*(∫ v in nearDomain,
    {v : Param | P4poly v.1 v.2.1 v.2.2<0}.indicator
      (fun v => if isCommon (centers v) i j then weight v*g (dist (centers v i) (centers v j)) else 0) v ∂pathMeasure)=_
  rw [setIntegral_indicator hm]
  rfl

private theorem HardSphereB5.Lean.Geometry.PathCore.s4_near_pair_split (hwidth : S4PairWidthSignature) (i j : Fin 4) (hij : i≠j)
  (hF : Integrable (s4FaceArc i j (oth1 i j) (oth2 i j)) (pathMeasure.restrict nearDomain))
  (hG : Integrable (s4FaceArc i j (oth2 i j) (oth1 i j)) (pathMeasure.restrict nearDomain))
  (hB : Integrable (s4BulkArc i j) (pathMeasure.restrict nearDomain))
  (hC : Integrable (s4CorrectionArc i j) (pathMeasure.restrict nearDomain)) :
  nearPairArc i j=triangleSide i j (oth1 i j) (oth2 i j)+
    triangleSide i j (oth2 i j) (oth1 i j)+bulkSource i j+nearCorrection i j := by
  have heq : (fun v => weight v*g (dist (centers v i) (centers v j))*ell (centers v) i j)=ᵐ[pathMeasure.restrict nearDomain]
    (fun v => s4FaceArc i j (oth1 i j) (oth2 i j) v+
      s4FaceArc i j (oth2 i j) (oth1 i j) v-s4BulkArc i j v-2*π*s4CorrectionArc i j v) := by
    filter_upwards [ae_restrict_of_ae path_ae_support,ae_restrict_of_ae path_ae_p4_ne] with v hv hP
    rcases hv with ⟨hX,hX1,hY,hY1,hH⟩
    have hc : IsPathConfig (centers v) v.1 v.2.1 v.2.2 := canonical_config hX hX1 hY hY1 hH
    rw [hwidth hc hP i j hij]
    simp only [s4FaceArc,s4BulkArc,s4CorrectionArc]
    by_cases hb : 0<P4poly v.1 v.2.1 v.2.2 <;>
      by_cases hs : P4poly v.1 v.2.1 v.2.2<0 <;>
      by_cases hc : isCommon (centers v) i j
    all_goals simp only [hb,hs,hc,and_self,ite_true,ite_false,and_false,false_and]
    all_goals ring
  unfold nearPairArc
  rw [integral_congr_ae heq]
  have hs1 : (∫ v in nearDomain, s4FaceArc i j (oth1 i j) (oth2 i j) v+
      s4FaceArc i j (oth2 i j) (oth1 i j) v-s4BulkArc i j v-2*π*s4CorrectionArc i j v ∂pathMeasure)=
    (∫ v in nearDomain, s4FaceArc i j (oth1 i j) (oth2 i j) v+
      s4FaceArc i j (oth2 i j) (oth1 i j) v-s4BulkArc i j v ∂pathMeasure)-
    (∫ v in nearDomain,2*π*s4CorrectionArc i j v ∂pathMeasure) := by
      simpa only [Pi.sub_apply,Pi.add_apply] using integral_sub ((hF.add hG).sub hB) (hC.const_mul (2*π))
  have hs2 : (∫ v in nearDomain, s4FaceArc i j (oth1 i j) (oth2 i j) v+
      s4FaceArc i j (oth2 i j) (oth1 i j) v-s4BulkArc i j v ∂pathMeasure)=
    (∫ v in nearDomain, s4FaceArc i j (oth1 i j) (oth2 i j) v+
      s4FaceArc i j (oth2 i j) (oth1 i j) v ∂pathMeasure)-
    (∫ v in nearDomain,s4BulkArc i j v ∂pathMeasure) := by
      simpa only [Pi.sub_apply,Pi.add_apply] using integral_sub (hF.add hG) hB
  have hs3 : (∫ v in nearDomain, s4FaceArc i j (oth1 i j) (oth2 i j) v+
      s4FaceArc i j (oth2 i j) (oth1 i j) v ∂pathMeasure)=
    (∫ v in nearDomain,s4FaceArc i j (oth1 i j) (oth2 i j) v ∂pathMeasure)+
    (∫ v in nearDomain,s4FaceArc i j (oth2 i j) (oth1 i j) v ∂pathMeasure) := by
      simpa only [Pi.add_apply] using integral_add hF hG
  rw [hs1,hs2,hs3,integral_const_mul]
  change (-1/2:ℝ)*((∫ v in nearDomain,s4FaceArc i j (oth1 i j) (oth2 i j) v ∂pathMeasure)+
    (∫ v in nearDomain,s4FaceArc i j (oth2 i j) (oth1 i j) v ∂pathMeasure)-
    (∫ v in nearDomain,s4BulkArc i j v ∂pathMeasure)-
    (2*π)*(∫ v in nearDomain,s4CorrectionArc i j v ∂pathMeasure))=_
  rw [←s4_bulk_integral i j,←s4_correction_integral i j]
  unfold triangleSide
  simp only [s4FaceArc]
  ring

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
private def HardSphereB5.Lean.Geometry.PathCore.S4ArcLabelTransport : Prop :=
  triangleSide 0 1 3 2=triangleSide 0 1 2 3 ∧
  triangleSide 0 2 1 3=triangleSide 0 1 2 3 ∧
  triangleSide 1 3 0 2=triangleSide 0 1 2 3 ∧
  triangleSide 0 3 1 2=triangleSide 1 2 0 3 ∧
  triangleSide 1 3 2 0=triangleSide 0 2 3 1 ∧
  triangleSide 1 2 3 0=triangleSide 0 3 2 1 ∧
  triangleSide 2 3 1 0=triangleSide 2 3 0 1 ∧
  bulkSource 1 3=bulkSource 0 2 ∧ bulkSource 0 3=bulkSource 1 2

private theorem HardSphereB5.Lean.Geometry.PathCore.s4_inventory_collection
  (hsplit : ∀ i j : Fin 4, i≠j → nearPairArc i j=
    triangleSide i j (oth1 i j) (oth2 i j)+triangleSide i j (oth2 i j) (oth1 i j)+
    bulkSource i j+nearCorrection i j)
  (htransport : S4ArcLabelTransport)
  (hcorrection : nearCorrection 0 2=Ssliver/2 ∧ nearCorrection 1 3=Ssliver/2 ∧
    nearCorrection 0 1=0 ∧ nearCorrection 1 2=0 ∧ nearCorrection 0 3=0 ∧ nearCorrection 2 3=0) :
  (∑ i, ∑ j, (if i<j then nearPairArc i j else 0)) =
    4*triangleSide 0 1 2 3 + 2*triangleSide 1 2 0 3 + 2*triangleSide 0 2 3 1 +
    2*triangleSide 0 3 2 1 + 2*triangleSide 2 3 0 1 +
    bulkSource 0 1 + 2*bulkSource 0 2 + 2*bulkSource 1 2 + bulkSource 2 3 + Ssliver := by
  rcases htransport with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  rcases hcorrection with ⟨c02,c13,c01,c12,c03,c23⟩
  have ho1_01 : oth1 (0:Fin 4) 1=2 := by decide
  have ho2_01 : oth2 (0:Fin 4) 1=3 := by decide
  have ho1_02 : oth1 (0:Fin 4) 2=1 := by decide
  have ho2_02 : oth2 (0:Fin 4) 2=3 := by decide
  have ho1_03 : oth1 (0:Fin 4) 3=1 := by decide
  have ho2_03 : oth2 (0:Fin 4) 3=2 := by decide
  have ho1_12 : oth1 (1:Fin 4) 2=0 := by decide
  have ho2_12 : oth2 (1:Fin 4) 2=3 := by decide
  have ho1_13 : oth1 (1:Fin 4) 3=0 := by decide
  have ho2_13 : oth2 (1:Fin 4) 3=2 := by decide
  have ho1_23 : oth1 (2:Fin 4) 3=0 := by decide
  have ho2_23 : oth2 (2:Fin 4) 3=1 := by decide
  simp only [Fin.sum_univ_four,(show ¬((0:Fin 4)<0) by decide),(show (0:Fin 4)<1 by decide),(show (0:Fin 4)<2 by decide),(show (0:Fin 4)<3 by decide),(show ¬((1:Fin 4)<0) by decide),(show ¬((1:Fin 4)<1) by decide),(show (1:Fin 4)<2 by decide),(show (1:Fin 4)<3 by decide),(show ¬((2:Fin 4)<0) by decide),(show ¬((2:Fin 4)<1) by decide),(show ¬((2:Fin 4)<2) by decide),(show (2:Fin 4)<3 by decide),(show ¬((3:Fin 4)<0) by decide),(show ¬((3:Fin 4)<1) by decide),(show ¬((3:Fin 4)<2) by decide),(show ¬((3:Fin 4)<3) by decide),ite_true,ite_false,zero_add,add_zero]
  rw [hsplit 0 1 (by decide),hsplit 0 2 (by decide),hsplit 0 3 (by decide),hsplit 1 2 (by decide),hsplit 1 3 (by decide),hsplit 2 3 (by decide)]
  simp only [ho1_01,ho2_01,ho1_02,ho2_02,ho1_03,ho2_03,ho1_12,ho2_12,ho1_13,ho2_13,ho1_23,ho2_23]
  rw [h1,h2,h3,h4,h5,h6,h7,h8,h9,c02,c13,c01,c12,c03,c23]
  ring

open HardSphereB5.Lean.Geometry.PathCore
open MeasureTheory Real
open scoped Classical
private lemma HardSphereB5.Lean.Geometry.PathCore.s4f_bulk_integrable (i j : Fin 4) : Integrable (s4BulkArc i j) (pathMeasure.restrict nearDomain) := by
  have hi : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if 0<P4poly v.1 v.2.1 v.2.2 then phiE (centers v) i j else 0)) (pathMeasure.restrict nearDomain) := conditional_phi_integrable i j
  have heq : (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if 0<P4poly v.1 v.2.1 v.2.2 then phiE (centers v) i j else 0))=s4BulkArc i j := by
    funext v
    by_cases h : 0<P4poly v.1 v.2.1 v.2.2 <;> simp [s4BulkArc,h]
  rw [heq] at hi
  exact hi
private lemma HardSphereB5.Lean.Geometry.PathCore.s4f_correction_integrable (i j : Fin 4) : Integrable (s4CorrectionArc i j) (pathMeasure.restrict nearDomain) := by
  have hi : Integrable (fun v => weight v*g (dist (centers v i) (centers v j))*
      (if P4poly v.1 v.2.1 v.2.2<0 ∧ isCommon (centers v) i j then 2*π else 0)) (pathMeasure.restrict nearDomain) := weighted_correction_integrable i j
  have hd := hi.div_const (2*π)
  have heq : (fun v => (weight v*g (dist (centers v i) (centers v j))*
      (if P4poly v.1 v.2.1 v.2.2<0 ∧ isCommon (centers v) i j then 2*π else 0))/(2*π))=s4CorrectionArc i j := by
    funext v
    by_cases hp : P4poly v.1 v.2.1 v.2.2<0 <;> by_cases hc : isCommon (centers v) i j
    all_goals simp [s4CorrectionArc,hp,hc,Real.pi_ne_zero]
  rw [heq] at hd
  exact hd
private lemma HardSphereB5.Lean.Geometry.PathCore.s4f_pair_split (hwidth : S4PairWidthSignature) (i j : Fin 4) (hij : i≠j) :
    nearPairArc i j=triangleSide i j (oth1 i j) (oth2 i j)+
      triangleSide i j (oth2 i j) (oth1 i j)+bulkSource i j+nearCorrection i j := by
  refine s4_near_pair_split hwidth i j hij ?_ ?_ (s4f_bulk_integrable i j) (s4f_correction_integrable i j)
  · convert weighted_triangle_integrable i j (oth1 i j) (oth2 i j) using 1 <;> try rfl
  · convert weighted_triangle_integrable i j (oth2 i j) (oth1 i j) using 1 <;> try rfl

private theorem HardSphereB5.Lean.Geometry.PathCore.near_arc_inventory_of_deps (hwidth : S4PairWidthSignature) :
    (∑ i, ∑ j, (if i<j then nearPairArc i j else 0)) =
      4*triangleSide 0 1 2 3 + 2*triangleSide 1 2 0 3 + 2*triangleSide 0 2 3 1 +
      2*triangleSide 0 3 2 1 + 2*triangleSide 2 3 0 1 +
      bulkSource 0 1 + 2*bulkSource 0 2 + 2*bulkSource 1 2 + bulkSource 2 3 + Ssliver := by
  exact s4_inventory_collection (s4f_pair_split hwidth) s4_arc_label_transport equal_sliver_halves

open HardSphereB5.Lean.Geometry.PathCore
private theorem HardSphereB5.Lean.Geometry.PathCore.near_arc_inventory_s5proof : (∑ i, ∑ j, (if i<j then nearPairArc i j else 0)) =
  4*triangleSide 0 1 2 3 + 2*triangleSide 1 2 0 3 + 2*triangleSide 0 2 3 1 +
  2*triangleSide 0 3 2 1 + 2*triangleSide 2 3 0 1 +
  bulkSource 0 1 + 2*bulkSource 0 2 + 2*bulkSource 1 2 + bulkSource 2 3 + Ssliver := by
  exact near_arc_inventory_of_deps pair_width

open HardSphereB5.Lean.Geometry.PathCore HardSphereB5.Lean MeasureTheory Real
open scoped Classical
theorem proof_HardSphereB5_Lean_Geometry_PathCore_near_arc_inventory : (∑ i, ∑ j, (if i<j then nearPairArc i j else 0)) =
  4*triangleSide 0 1 2 3 + 2*triangleSide 1 2 0 3 + 2*triangleSide 0 2 3 1 +
  2*triangleSide 0 3 2 1 + 2*triangleSide 2 3 0 1 +
  bulkSource 0 1 + 2*bulkSource 0 2 + 2*bulkSource 1 2 + bulkSource 2 3 + Ssliver := by
  exact @HardSphereB5.Lean.Geometry.PathCore.near_arc_inventory_s5proof
