import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_arcMeasure_restrict_circle
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_cross_norm_sq
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 1800000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_circInt_bound (p p' : Pt) (hp : p ∈ FA) (hp' : p' ∈ FB)
    (hd0 : 0 < dist p p') (hd1 : dist p p' < 1) :
    |circInt p p'| ≤ 2 * Real.pi * (dist p p') ^ 2 := by
  classical
  let n : (Pt × Pt) → Pt := fun p => unitDir (p.2-p.1)
  let w : (Pt × Pt) → Pt := fun p => e-n p
  let R : (Pt × Pt) → Pt ≃ₗᵢ[ℝ] Pt := fun p => (ℝ ∙ w p)ᗮ.reflection
  let E : (Pt × Pt) → Fin 2 → Pt := fun p i => R p (![e1,e2] i)
  let q : (Pt × Pt) → ℝ → Pt := fun p t => circlePt 0 (E p 0) (E p 1) 1 t
  let a : (Pt × Pt) → Pt → ℝ := fun p x =>
    (1-dist p.1 p.2^2/4) * inner ℝ x (NAv p.1 p.2) * inner ℝ x (NBv p.1 p.2)
  let L : Set ((Pt × Pt) × Pt) := {v |
    midpoint ℝ v.1.1 v.1.2 + √(1-dist v.1.1 v.1.2^2/4) • v.2 ∈ LamC}
  let G : ((Pt × Pt) × Pt) → ℝ := L.indicator (Function.uncurry a)
  let Q : ((Pt × Pt) × ℝ) → ℝ := fun v => G (v.1, q v.1 v.2)
  have hnmeas : Measurable n := by dsimp [n, unitDir]; fun_prop
  have hwmeas : Measurable w := measurable_const.sub hnmeas
  have hRf (p : Pt × Pt) (u : Pt) : R p u =
      u - (2 : ℝ) • ((inner ℝ (w p) u / ‖w p‖^2) • w p) := by
    dsimp only [R]
    rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
    simp only [neg_sub]
    module
  have hRmeas (u : Pt) : Measurable (fun p => R p u) := by
    simp_rw [hRf]
    fun_prop
  have hEmeas (i : Fin 2) : Measurable (fun p => E p i) := hRmeas _
  have hqmeas : Measurable (Function.uncurry q) := by
    dsimp [q, circlePt]
    fun_prop
  have hL : MeasurableSet L := by
    apply MeasurableSet.preimage (measurableSet_closedBall.inter measurableSet_closedBall)
    change Measurable (fun v : (Pt × Pt) × Pt =>
      midpoint ℝ v.1.1 v.1.2 + √(1-dist v.1.1 v.1.2^2/4) • v.2)
    simp only [midpoint_eq_smul_add]
    fun_prop
  have ha : Measurable (Function.uncurry a) := by
    dsimp [a, NAv, NBv, cross]
    fun_prop
  have hG : Measurable G := ha.indicator hL
  have hQ : Measurable Q := hG.comp (measurable_fst.prodMk hqmeas)
  have he0 : Orthonormal ℝ (![e1,e2] : Fin 2 → Pt) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e1,e2,EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  have hE (p : Pt × Pt) : Orthonormal ℝ (E p) := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℝ (R p (![e1,e2] i)) (R p (![e1,e2] j)) = _
    rw [(R p).inner_map_map]
    exact orthonormal_iff_ite.mp he0 i j
  have hn (p : Pt × Pt) (hp : p.1 ≠ p.2) : ‖n p‖ = 1 := by
    dsimp [n, unitDir]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (norm_pos_iff.2 (sub_ne_zero.mpr hp.symm))),
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (sub_ne_zero.mpr hp.symm))]
  have hRe (p : Pt × Pt) (hp : p.1 ≠ p.2) : R p e = n p := by
    apply Submodule.reflection_sub
    rw [hn p hp]
    simp [HardSphereB5.Lean.e, EuclideanSpace.norm_single]
  have hcircle (p : Pt × Pt) (hp : p.1 ≠ p.2) :
      q p '' Set.Icc (0 : ℝ) (2*π) = {x : Pt | ‖x‖=1 ∧ inner ℝ x (p.2-p.1)=0} := by
    have hqeq (t : ℝ) : q p t = R p (Real.cos t • e1 + Real.sin t • e2) := by
      simp [q, circlePt, E]
    have hdn : p.2-p.1 = ‖p.2-p.1‖ • n p := by
      dsimp [n,unitDir]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 (sub_ne_zero.mpr hp.symm)), one_smul]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [hqeq]
      constructor
      · rw [(R p).norm_map]
        have hs : ‖Real.cos t • e1 + Real.sin t • e2‖^2=1 := by
          simp [e1,e2,EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,
            EuclideanSpace.single_apply,Real.sin_sq_add_cos_sq,Real.cos_sq_add_sin_sq]
        nlinarith [norm_nonneg (Real.cos t • e1 + Real.sin t • e2)]
      · rw [hdn, inner_smul_right, ← hRe p hp, (R p).inner_map_map]
        simp [e1,e2,HardSphereB5.Lean.e,inner_add_left,EuclideanSpace.inner_single_right]
    · intro hx
      let y : Pt := (R p).symm x
      have hyN : ‖y‖=1 := by simpa [y] using hx.1
      have hy0 : y 0=0 := by
        have hxy : x=R p y := by simp [y]
        have hxyinn := hx.2
        rw [hxy, hdn, ← hRe p hp, inner_smul_right, (R p).inner_map_map] at hxyinn
        have : inner ℝ y e=0 := (mul_eq_zero.mp hxyinn).resolve_left
          (norm_ne_zero_iff.2 (sub_ne_zero.mpr hp.symm))
        simpa [HardSphereB5.Lean.e, EuclideanSpace.inner_single_right] using this
      let z : ℂ := ⟨y 1,y 2⟩
      have hz : z ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
        rw [Metric.mem_sphere,dist_zero_right]
        have hysq : (y 1)^2+(y 2)^2=1 := by
          have hysq := congrArg (fun r : ℝ => r^2) hyN
          simpa [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,hy0,Real.norm_eq_abs,sq_abs] using hysq
        have hzsq : ‖z‖^2=1 := by
          rw [Complex.sq_norm]
          simpa [Complex.normSq_apply,z,pow_two] using hysq
        norm_num
        nlinarith [norm_nonneg z]
      rw [← image_circleMap_Ioc (0 : ℂ) 1] at hz
      rcases hz with ⟨t,ht,hzt⟩
      refine ⟨t,⟨ht.1.le,ht.2⟩,?_⟩
      have hc : Real.cos t=y 1 := by
        have h := congrArg Complex.re hzt
        simpa only [circleMap_zero_re,one_mul,z] using h
      have hs : Real.sin t=y 2 := by
        have h := congrArg Complex.im hzt
        simpa only [circleMap_zero_im,one_mul,z] using h
      have hyr : Real.cos t • e1 + Real.sin t • e2=y := by
        ext i
        fin_cases i <;> simp [e1,e2,EuclideanSpace.single_apply,hc,hs,hy0]
      rw [hqeq,hyr]
      simp [y]
  have hformula (p : Pt × Pt) (hp : p.1 ≠ p.2) :
      circInt p.1 p.2 = ∫ t in Set.Icc (0 : ℝ) (2*π), Q (p,t) := by
    let C : Set Pt := {x : Pt | ‖x‖=1 ∧ inner ℝ x (p.2-p.1)=0}
    let A : Set Pt := {x | (p,x) ∈ L}
    have hA : MeasurableSet A := (measurable_const.prodMk measurable_id) hL
    have hC : MeasurableSet C :=
      (isClosed_eq continuous_norm continuous_const).measurableSet.inter
        (isClosed_eq (continuous_id.inner continuous_const) continuous_const).measurableSet
    have hGq : Measurable (fun x => G (p,x)) := hG.comp (measurable_const.prodMk measurable_id)
    have hmq : Measurable (q p) := by dsimp [q,circlePt]; fun_prop
    have hm := SphereGeom.arcMeasure_restrict_circle (0 : Pt) (E p) (hE p) 1
      (by norm_num) 0 (2*π) (by positivity) (by simp)
    change arcMeasure.restrict (q p '' Set.Icc (0 : ℝ) (2*π)) =
      ENNReal.ofReal 1 • (volume.restrict (Set.Icc (0 : ℝ) (2*π))).map (q p) at hm
    simp only [ENNReal.ofReal_one,one_smul] at hm
    rw [hcircle p hp] at hm
    calc
      circInt p.1 p.2 = ∫ x in C, G (p,x) ∂arcMeasure := by
        dsimp only [G]
        rw [show (fun x => L.indicator (Function.uncurry a) (p,x))=A.indicator (a p) by rfl,
          integral_indicator hA,Measure.restrict_restrict hA]
        have hs : {x : Pt | ‖x‖=1 ∧ inner ℝ x (p.2-p.1)=0 ∧
            midpoint ℝ p.1 p.2 + √(1-dist p.1 p.2^2/4) • x ∈ LamC} = A ∩ C := by
          ext x
          simp [A,C,L,and_assoc,and_left_comm,and_comm]
        change ∫ x in {x : Pt | ‖x‖=1 ∧ inner ℝ x (p.2-p.1)=0 ∧
          midpoint ℝ p.1 p.2 + √(1-dist p.1 p.2^2/4) • x ∈ LamC}, a p x ∂arcMeasure =
          ∫ x in A ∩ C, a p x ∂arcMeasure
        rw [hs]
      _ = ∫ x, G (p,x) ∂(volume.restrict (Set.Icc (0 : ℝ) (2*π))).map (q p) := by rw [hm]
      _ = ∫ t in Set.Icc (0 : ℝ) (2*π), Q (p,t) := by
        rw [integral_map hmq.aemeasurable hGq.aestronglyMeasurable]
  have hpN : ‖p‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hp.1
  have hp'N : ‖p' - e‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hp'.1
  have hdnorm : ‖p' - p‖ = dist p p' := by
    rw [← dist_eq_norm, dist_comm]
  have hNA : ‖NAv p p'‖ ≤ dist p p' := by
    apply (sq_le_sq₀ (norm_nonneg _) hd0.le).mp
    change ‖cross p (p' - p)‖ ^ 2 ≤ (dist p p') ^ 2
    rw [SphereGeom.Aux.Santalo.cross_norm_sq, hpN, hdnorm]
    nlinarith [sq_nonneg (inner ℝ p (p' - p))]
  have hNB : ‖NBv p p'‖ ≤ dist p p' := by
    apply (sq_le_sq₀ (norm_nonneg _) hd0.le).mp
    change ‖cross (p' - e) (p' - p)‖ ^ 2 ≤ (dist p p') ^ 2
    rw [SphereGeom.Aux.Santalo.cross_norm_sq, hp'N, hdnorm]
    nlinarith [sq_nonneg (inner ℝ (p' - e) (p' - p))]
  have hd2 : (dist p p') ^ 2 < 1 := by
    simpa [pow_two] using mul_self_lt_mul_self hd0.le hd1
  have hr0 : 0 ≤ 1 - (dist p p') ^ 2 / 4 := by nlinarith
  have hr1 : 1 - (dist p p') ^ 2 / 4 ≤ 1 := by
    nlinarith [sq_nonneg (dist p p')]
  have hQbd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (2*π)) :
      ‖Q ((p,p'),t)‖ ≤ (dist p p') ^ 2 := by
    have hqN : ‖q (p,p') t‖ = 1 := by
      have hx : q (p,p') t ∈ q (p,p') '' Set.Icc (0 : ℝ) (2*π) := ⟨t, ht, rfl⟩
      rw [hcircle (p,p') (dist_pos.mp hd0)] at hx
      exact hx.1
    have hI1 : |inner ℝ (q (p,p') t) (NAv p p')| ≤ dist p p' := by
      calc
        _ ≤ ‖q (p,p') t‖ * ‖NAv p p'‖ := abs_real_inner_le_norm _ _
        _ ≤ dist p p' := by simpa only [hqN, one_mul] using hNA
    have hI2 : |inner ℝ (q (p,p') t) (NBv p p')| ≤ dist p p' := by
      calc
        _ ≤ ‖q (p,p') t‖ * ‖NBv p p'‖ := abs_real_inner_le_norm _ _
        _ ≤ dist p p' := by simpa only [hqN, one_mul] using hNB
    change ‖L.indicator (Function.uncurry a) ((p,p'), q (p,p') t)‖ ≤ _
    by_cases hLq : ((p,p'), q (p,p') t) ∈ L
    · rw [Set.indicator_of_mem hLq]
      change ‖(1 - (dist p p') ^ 2 / 4) * inner ℝ (q (p,p') t) (NAv p p') *
        inner ℝ (q (p,p') t) (NBv p p')‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hr0]
      calc
        _ ≤ (1 * dist p p') * dist p p' :=
          mul_le_mul (mul_le_mul hr1 hI1 (abs_nonneg _) (by norm_num)) hI2
            (abs_nonneg _) (by positivity)
        _ = (dist p p') ^ 2 := by ring
    · rw [Set.indicator_of_notMem hLq, norm_zero]
      exact sq_nonneg _
  rw [hformula (p,p') (dist_pos.mp hd0), ← Real.norm_eq_abs]
  calc
    _ ≤ (dist p p') ^ 2 * volume.real (Set.Icc (0 : ℝ) (2*π)) :=
      norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Icc_lt_top hQbd
    _ = 2 * π * (dist p p') ^ 2 := by
      rw [Real.volume_real_Icc_of_le (by positivity)]
      ring
