import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_cylinder
set_option autoImplicit false
open MeasureTheory Real SphereGeom Set
open scoped ENNReal
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000
private theorem planar :
    Measure.map (fun zφ : ℝ × ℝ =>
      (Real.sqrt (1 - zφ.1 ^ 2) * Real.cos zφ.2,
       Real.sqrt (1 - zφ.1 ^ 2) * Real.sin zφ.2))
      ((((volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ico 0 (2 * Real.pi))).withDensity
          (fun zφ => ENNReal.ofReal zφ.1))) =
      (volume : Measure (ℝ × ℝ)).restrict {p | p.1 ^ 2 + p.2 ^ 2 < 1} := by
  let R : ℝ → ℝ := fun z => sqrt (1 - z ^ 2)
  let F : ℝ × ℝ → ℝ × ℝ := fun p => (R p.1 * cos p.2, R p.1 * sin p.2)
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo 0 (2 * π)
  let B : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 < 1}
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have rpos (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) : 0 < R z := by
    apply sqrt_pos.2
    nlinarith [hz.1,hz.2]
  have rsq (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) : R z ^ 2 = 1 - z ^ 2 := by
    exact sq_sqrt (by nlinarith [hz.1,hz.2])
  have rder (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) : HasDerivAt R (-z / R z) z := by
    have d : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * z) z := by
      convert! ((hasDerivAt_id z).pow 2).const_sub 1 using 1 <;> simp [id_eq]
    convert! d.sqrt (by nlinarith [hz.1, hz.2]) using 1
    dsimp [R]
    ring
  let D : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ × ℝ) := fun p =>
    (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
      !![(-p.1 / R p.1) * cos p.2, -(R p.1) * sin p.2;
         (-p.1 / R p.1) * sin p.2, R p.1 * cos p.2]).toContinuousLinearMap
  have fder (p : ℝ × ℝ) (hp : p ∈ S) : HasFDerivAt F (D p) p := by
    dsimp [D]
    rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
    convert! HasFDerivAt.prodMk (𝕜 := ℝ)
      (((rder p.1 hp.1).comp_hasFDerivAt p hasFDerivAt_fst).mul
        ((hasDerivAt_cos p.2).comp_hasFDerivAt p hasFDerivAt_snd))
      (((rder p.1 hp.1).comp_hasFDerivAt p hasFDerivAt_fst).mul
        ((hasDerivAt_sin p.2).comp_hasFDerivAt p hasFDerivAt_snd)) using 2 <;>
      simp [F, smul_smul, add_comm, mul_comm, neg_mul, smul_neg,
        neg_smul _ (ContinuousLinearMap.snd ℝ ℝ ℝ)]
  have detD (p : ℝ × ℝ) (hp : p ∈ S) : |(D p).det| = p.1 := by
    have hr := (rpos p.1 hp.1).ne'
    have hdet : (D p).det = -p.1 := by
      dsimp [D]
      simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
        Matrix.det_fin_two_of]
      field_simp
      linear_combination -p.1 * cos_sq_add_sin_sq p.2
    rw [hdet, abs_neg, abs_of_pos hp.1.1]
  have shift (p : ℝ × ℝ) :
      F p = -polarCoord.symm (R p.1, p.2 - π) := by
    ext <;> simp [F, polarCoord_symm_apply, cos_sub_pi, sin_sub_pi]
  have hinj : InjOn F S := by
    intro p hp q hq he
    have hp' : (R p.1, p.2 - π) ∈ polarCoord.target := by
      change 0 < R p.1 ∧ -π < p.2 - π ∧ p.2 - π < π
      exact ⟨rpos _ hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hq' : (R q.1, q.2 - π) ∈ polarCoord.target := by
      change 0 < R q.1 ∧ -π < q.2 - π ∧ q.2 - π < π
      exact ⟨rpos _ hq.1, by linarith [hq.2.1], by linarith [hq.2.2]⟩
    rw [shift, shift] at he
    have he' := polarCoord.symm.injOn hp' hq' (neg_injective he)
    have heR := congrArg Prod.fst he'
    have heA := congrArg Prod.snd he'
    dsimp at heR heA
    have heZ : p.1 = q.1 := by
      have h1 := rsq p.1 hp.1
      have h2 := rsq q.1 hq.1
      rw [heR] at h1
      nlinarith [hp.1.1,hq.1.1]
    exact Prod.ext heZ (by linarith)
  have hnorm (p : ℝ × ℝ) : (F p).1 ^ 2 + (F p).2 ^ 2 = R p.1 ^ 2 := by
    dsimp [F]
    nlinarith [cos_sq_add_sin_sq p.2]
  have himg_sub : F '' S ⊆ B := by
    rintro v ⟨p,hp,rfl⟩
    change (F p).1 ^ 2 + (F p).2 ^ 2 < 1
    rw [hnorm, rsq p.1 hp.1]
    nlinarith [hp.1.1]
  have himg_large (v : ℝ × ℝ) (hv : v ∈ B) (hy : v.2 ≠ 0) : v ∈ F '' S := by
    have hsrc : -v ∈ polarCoord.source := by
      change 0 < (-v).1 ∨ (-v).2 ≠ 0
      right
      simpa using hy
    let a := polarCoord (-v)
    have hat : a ∈ polarCoord.target := polarCoord.map_source hsrc
    have har : 0 < a.1 := hat.1
    have har2 : a.1 ^ 2 = v.1 ^ 2 + v.2 ^ 2 := by
      dsimp [a, polarCoord]
      simpa using sq_sqrt (show 0 ≤ (-v).1 ^ 2 + (-v).2 ^ 2 by positivity)
    have halt : a.1 < 1 := by
      dsimp [B] at hv
      nlinarith
    let z : ℝ := sqrt (1 - a.1 ^ 2)
    have hzpos : 0 < z := sqrt_pos.2 (by nlinarith)
    have hzsq : z ^ 2 = 1 - a.1 ^ 2 := sq_sqrt (by nlinarith)
    have hzlt : z < 1 := by nlinarith [sq_pos_of_pos har]
    have hrz : R z = a.1 := by
      dsimp [R]
      have he : 1 - z ^ 2 = a.1 ^ 2 := by linarith
      rw [he, sqrt_sq har.le]
    refine ⟨(z, a.2 + π), ⟨⟨hzpos,hzlt⟩,?_⟩,?_⟩
    · exact ⟨by linarith [hat.2.1], by linarith [hat.2.2]⟩
    · rw [shift]
      simp only [Prod.fst,Prod.snd,add_sub_cancel_right,hrz]
      change -polarCoord.symm (polarCoord (-v)) = v
      rw [polarCoord.left_inv hsrc,neg_neg]
  have hy_ae : ∀ᵐ v : ℝ × ℝ ∂volume, v.2 ≠ 0 := by
    have hh : (volume : Measure (ℝ × ℝ)) (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) : Set (ℝ × ℝ)) = 0 := by
      apply Measure.addHaar_submodule
      rw [Ne, LinearMap.ker_eq_top]
      intro h
      have he : (LinearMap.snd ℝ ℝ ℝ) (0,1) = (0 : ℝ × ℝ →ₗ[ℝ] ℝ) (0,1) := by rw [h]
      simp at he
    have hk : (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) : Set (ℝ × ℝ)) =
        {v : ℝ × ℝ | v.2 = 0} := by ext v; rfl
    rw [hk] at hh
    apply ae_iff.2
    simpa only [mem_setOf_eq, Classical.not_not] using hh
  have himg_ae : F '' S =ᵐ[volume] B := by
    filter_upwards [hy_ae] with v hy
    exact propext ⟨fun hv => himg_sub hv,fun hv => himg_large v hv hy⟩
  have hmap : Measure.map F (((volume : Measure (ℝ × ℝ)).restrict S).withDensity
      (fun p => ENNReal.ofReal p.1)) = (volume : Measure (ℝ × ℝ)).restrict B := by
    have hd : (((volume : Measure (ℝ × ℝ)).restrict S).withDensity
        (fun p => ENNReal.ofReal p.1)) =
        (((volume : Measure (ℝ × ℝ)).restrict S).withDensity
        (fun p => ENNReal.ofReal |(D p).det|)) := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hS] with p hp
      rw [detD p hp]
    rw [hd, map_withDensity_abs_det_fderiv_eq_addHaar volume hS.nullMeasurableSet
      (fun p hp => (fder p hp).hasFDerivWithinAt) hinj,
      Measure.restrict_congr_set himg_ae]
  have hend : (volume : Measure (ℝ × ℝ)).restrict
        (Ioc (0 : ℝ) 1 ×ˢ Ico 0 (2 * π)) =
      (volume : Measure (ℝ × ℝ)).restrict S := by
    change ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict _ =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict _
    rw [← Measure.prod_restrict, ← Measure.prod_restrict]
    rw [← restrict_Ioo_eq_restrict_Ioc, ← restrict_Ioo_eq_restrict_Ico]
  change Measure.map F (((volume : Measure (ℝ × ℝ)).restrict
      (Ioc (0 : ℝ) 1 ×ˢ Ico 0 (2 * π))).withDensity (fun p => ENNReal.ofReal p.1)) = _
  rw [hend]
  exact hmap

private theorem map_density {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (f : A → B) (g : B → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) : (μ.map f).withDensity g = (μ.withDensity (fun x => g (f x))).map f := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_withDensity_eq_lintegral_mul _ hg hφ,
    lintegral_map (hg.mul hφ) hf, lintegral_map hφ hf]
  rw [lintegral_withDensity_eq_lintegral_mul _
    (show Measurable (fun x => g (f x)) from hg.comp hf)
    (show Measurable (fun x => φ (f x)) from hφ.comp hf)]
  rfl
theorem proof_SolidGeom_sphere_upper_projection (c : E3) (e : Fin 3 → E3) (he : Orthonormal ℝ e) :
    Measure.map (fun x : E3 => (inner ℝ (e 0) x, inner ℝ (e 1) x))
      (((sphereMeasure c).restrict {x : E3 | 0 < inner ℝ (e 2) (x - c)}).withDensity
        (fun x => ENNReal.ofReal (inner ℝ (e 2) (x - c)))) =
    (volume : Measure (ℝ × ℝ)).restrict
      {p : ℝ × ℝ | (p.1 - inner ℝ (e 0) c) ^ 2 + (p.2 - inner ℝ (e 1) c) ^ 2 < 1} := by
  let C : ℝ×ℝ → E3 := fun p =>
    (sqrt (1-p.1^2)*cos p.2) • e 0 +
    (sqrt (1-p.1^2)*sin p.2) • e 1 + p.1 • e 2
  let A : Set (ℝ×ℝ) := Set.Icc (-1:ℝ) 1 ×ˢ Set.Ico 0 (2*π)
  let U : Set (ℝ×ℝ) := Set.Ioc (0:ℝ) 1 ×ˢ Set.Ico 0 (2*π)
  let D : ℝ×ℝ → ℝ×ℝ := fun p => (sqrt (1-p.1^2)*cos p.2, sqrt (1-p.1^2)*sin p.2)
  let P : E3 → ℝ×ℝ := fun x => (inner ℝ (e 0) x, inner ℝ (e 1) x)
  let T : ℝ×ℝ → ℝ×ℝ := fun p => P c + p
  have hC : Measurable C := by dsimp [C]; fun_prop
  have hP : Measurable P := by dsimp [P]; fun_prop
  have hT : Measurable T := by dsimp [T]; fun_prop
  have hA : MeasurableSet A := measurableSet_Icc.prod measurableSet_Ico
  have hU : MeasurableSet U := measurableSet_Ioc.prod measurableSet_Ico
  have hinner (i : Fin 3) (p : ℝ×ℝ) :
      inner ℝ (e i) (C p) = if i=0 then (D p).1 else if i=1 then (D p).2 else p.1 := by
    dsimp [C,D]
    simp only [inner_add_right, inner_smul_right, orthonormal_iff_ite.mp he]
    fin_cases i <;> simp
  have hN (p : ℝ×ℝ) : inner ℝ (e 2) ((c+C p)-c) = p.1 := by
    simp only [add_sub_cancel_left, hinner]
    simp only [show (2:Fin 3) ≠ 0 from by decide, show (2:Fin 3) ≠ 1 from by decide, if_false]
  have hPC : P ∘ (fun p => c+C p) = T ∘ D := by
    funext p
    dsimp [P,T,Function.comp_def]
    simp only [inner_add_right, hinner]
    norm_num [Fin.reduceEq]
    rfl
  have hsc : sphereMeasure c = ((volume : Measure (ℝ×ℝ)).restrict A).map (fun p => c+C p) := by
    have ht : sphereMeasure c = dOmega.map (fun u : E3 => c+u) := by
      dsimp [sphereMeasure,dOmega]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext u; simp
    rw [ht,SphereGeom.dOmega_map_cylinder e he,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hH : MeasurableSet {x : E3 | 0 < inner ℝ (e 2) (x-c)} := by
    apply isOpen_lt continuous_const (by fun_prop) |>.measurableSet
  have hmu : ((sphereMeasure c).restrict {x : E3 | 0 < inner ℝ (e 2) (x-c)}).withDensity
      (fun x => ENNReal.ofReal (inner ℝ (e 2) (x-c))) =
    ((((volume : Measure (ℝ×ℝ)).restrict U).withDensity (fun p => ENNReal.ofReal p.1))).map
      (fun p => c+C p) := by
    rw [hsc,Measure.restrict_map (by fun_prop) hH,
      map_density _ _ _ (by fun_prop) (by fun_prop)]
    have hs : A ∩ (fun p => c+C p) ⁻¹' {x | 0 < inner ℝ (e 2) (x-c)} = U := by
      ext p
      simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_setOf_eq,hN]
      dsimp [A,U]
      simp only [Set.mem_prod,Set.mem_Icc,Set.mem_Ioc]
      constructor
      · rintro ⟨⟨⟨ha,hb⟩,hc⟩,hd⟩; exact ⟨⟨hd,hb⟩,hc⟩
      · rintro ⟨⟨ha,hb⟩,hc⟩; exact ⟨⟨⟨by linarith,hb⟩,hc⟩,ha⟩
    rw [Measure.restrict_restrict ((show Measurable (fun p => c+C p) from by fun_prop) hH)]
    rw [Set.inter_comm,hs]
    simp only [hN]
  rw [hmu,Measure.map_map hP (by fun_prop)]
  change ((((volume : Measure (ℝ×ℝ)).restrict U).withDensity (fun p => ENNReal.ofReal p.1)).map (P ∘ (fun p => c+C p))) = _
  rw [hPC,← Measure.map_map hT (by dsimp [D]; fun_prop)]
  rw [show (((volume : Measure (ℝ×ℝ)).restrict U).withDensity (fun p => ENNReal.ofReal p.1)).map D =
      (volume : Measure (ℝ×ℝ)).restrict {p | p.1^2+p.2^2<1} from planar]
  have hvol : (volume : Measure (ℝ×ℝ)).map T = volume := by
    exact map_add_left_eq_self volume (P c)
  let B : Set (ℝ×ℝ) := {p | (p.1-inner ℝ (e 0) c)^2+(p.2-inner ℝ (e 1) c)^2<1}
  have hB : MeasurableSet B := by dsimp [B]; apply isOpen_lt (by fun_prop) continuous_const |>.measurableSet
  have hpre : T ⁻¹' B = {p : ℝ×ℝ | p.1^2+p.2^2<1} := by
    ext p
    dsimp [T,B,P]; simp
  rw [← hpre,← Measure.restrict_map hT hB,hvol]
