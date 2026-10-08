import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_lens_covered
import HardSphereB5Lean.Theorems.Thm_SolidGeom_sphereMeasure_sphere_inter_null
import HardSphereB5Lean.Theorems.Thm_SphereGeom_sphereMeasure_univ
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_pathFaceQ_pos
set_option autoImplicit false

noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 2000000
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private theorem mem_body (c : Fin 4 → Pt) (F : Finset (Fin 4)) (x : Pt) :
    x ∈ body c F ↔ ∀ i ∈ F, dist x (c i) ≤ 1 := by
  simp [body, Metric.mem_closedBall]

private theorem body_pair (c : Fin 4 → Pt) (i j : Fin 4) :
    body c {i,j} = Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1 := by
  ext x
  simp [mem_body, Metric.mem_closedBall]

private theorem body_measurable (c : Fin 4 → Pt) (F : Finset (Fin 4)) :
    MeasurableSet (body c F) := by
  unfold body
  exact MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ => measurableSet_closedBall))

private instance finite_sphere (c : Pt) : IsFiniteMeasure (sphereMeasure c) := by
  constructor
  rw [SphereGeom.sphereMeasure_univ]
  exact ENNReal.ofReal_lt_top

private theorem path_Q_pos (hc : IsPathConfig c X Y s) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : 0 < Qf c i j k := by
  exact HardSphereB5.Lean.Geometry.pathFaceQ_pos c X Y s hc.q01 hc.q02 hc.q03 hc.q12 hc.q13
    hc.q23 hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one hc.H_pos i j k hij hik hjk

private theorem measure_inter_valuation (μ : Measure Pt) (A B : Set Pt)
    (hB : MeasurableSet B) (hAfinite : μ A ≠ ⊤) (hBfinite : μ B ≠ ⊤) :
    (μ (A ∩ B)).toReal = (μ A).toReal + (μ B).toReal - (μ (A ∪ B)).toReal := by
  have hU : μ (A ∪ B) ≠ ⊤ := ne_of_lt <|
    lt_of_le_of_lt (measure_union_le A B) (ENNReal.add_lt_top.mpr ⟨hAfinite.lt_top, hBfinite.lt_top⟩)
  have hI : μ (A ∩ B) ≠ ⊤ := ne_of_lt <| lt_of_le_of_lt
    (measure_mono Set.inter_subset_left) hAfinite.lt_top
  have h := congrArg ENNReal.toReal (measure_union_add_inter (μ := μ) A hB)
  rw [ENNReal.toReal_add hU hI, ENNReal.toReal_add hAfinite hBfinite] at h
  linarith

private theorem integral_inter_valuation (μ : Measure Pt) (A B : Set Pt) (f : Pt → Pt)
    (hB : MeasurableSet B) (hfA : IntegrableOn f A μ) (hfB : IntegrableOn f B μ) :
    (∫ x in A ∩ B, f x ∂μ) = (∫ x in A, f x ∂μ) + (∫ x in B, f x ∂μ)
      - (∫ x in A ∪ B, f x ∂μ) := by
  have hU : (∫ x in A ∪ B, f x ∂μ) = (∫ x in A \ B, f x ∂μ) + (∫ x in B, f x ∂μ) := by
    rw [← Set.sdiff_union_self]
    exact setIntegral_union disjoint_sdiff_self_left hB (hfA.mono_set Set.sdiff_subset) hfB
  have hA := (integral_inter_add_sdiff hB hfA).symm
  rw [hU, hA]
  abel

private theorem body_integrable (c : Fin 4 → Pt) (m : Fin 4) (F : Finset (Fin 4))
    (hne : F.Nonempty) : IntegrableOn (fun x => x-c m) (body c F) (sphereMeasure (c m)) := by
  obtain ⟨i,hi⟩ := hne
  have hclosed : IsClosed (body c F) := by
    unfold body
    exact isClosed_iInter (fun _ => isClosed_iInter (fun _ => Metric.isClosed_closedBall))
  have hcompact : IsCompact (body c F) :=
    (isCompact_closedBall (c i) 1).of_isClosed_subset hclosed
      (fun x hx => (mem_body c F x).mp hx i hi)
  exact ContinuousOn.integrableOn_compact hcompact (continuous_id.sub continuous_const).continuousOn

private theorem sliver_common_patch_valuation (c : Fin 4 → Pt) (i j m : Fin 4)
    (hm : m = i ∨ m = j)
    (hCover : body c {i,j,oth1 i j} ∪ body c {i,j,oth2 i j} = body c {i,j})
    (hInter : body c {i,j,oth1 i j} ∩ body c {i,j,oth2 i j} = body c Finset.univ)
    (hf1 : IntegrableOn (fun x => x-c m) (body c {i,j,oth1 i j}) (sphereMeasure (c m)))
    (hf2 : IntegrableOn (fun x => x-c m) (body c {i,j,oth2 i j}) (sphereMeasure (c m))) :
    pArea c m Finset.univ = pArea c m {i,j,oth1 i j} + pArea c m {i,j,oth2 i j} - pArea c m {i,j} ∧
    pMoment c m Finset.univ = pMoment c m {i,j,oth1 i j} + pMoment c m {i,j,oth2 i j} - pMoment c m {i,j} := by
  have hm1 : m ∈ ({i,j,oth1 i j} : Finset (Fin 4)) := by rcases hm with rfl | rfl <;> simp
  have hm2 : m ∈ ({i,j,oth2 i j} : Finset (Fin 4)) := by rcases hm with rfl | rfl <;> simp
  have hmP : m ∈ ({i,j} : Finset (Fin 4)) := by rcases hm with rfl | rfl <;> simp
  constructor
  · simp only [pArea, hm1, hm2, hmP, Finset.mem_univ, if_true]
    have h := measure_inter_valuation (sphereMeasure (c m))
      (body c {i,j,oth1 i j}) (body c {i,j,oth2 i j}) (body_measurable _ _)
      (measure_ne_top _ _) (measure_ne_top _ _)
    simpa only [hCover,hInter] using h
  · simp only [pMoment, hm1, hm2, hmP, Finset.mem_univ, if_true]
    have h := integral_inter_valuation (sphereMeasure (c m))
      (body c {i,j,oth1 i j}) (body c {i,j,oth2 i j}) (fun x => x-c m)
      (body_measurable _ _) hf1 hf2
    simpa only [hCover,hInter] using h

private theorem others_distinct (i j : Fin 4) (hij : i ≠ j) :
    oth1 i j ≠ i ∧ oth1 i j ≠ j ∧ oth2 i j ≠ i ∧ oth2 i j ≠ j ∧ oth1 i j ≠ oth2 i j := by
  fin_cases i <;> fin_cases j <;> simp_all [oth1,oth2]

private theorem others_exhaust (i j m : Fin 4) (hij : i ≠ j)
    (hmi : m ≠ i) (hmj : m ≠ j) : m = oth1 i j ∨ m = oth2 i j := by
  fin_cases i <;> fin_cases j <;> fin_cases m <;> simp_all [oth1,oth2]

private theorem pair_bodies_inter (c : Fin 4 → Pt) (i j : Fin 4) (hij : i ≠ j) :
    body c {i,j,oth1 i j} ∩ body c {i,j,oth2 i j} = body c Finset.univ := by
  ext x
  simp only [Set.mem_inter_iff, mem_body]
  constructor
  · rintro ⟨h1,h2⟩ m _
    by_cases hmi : m = i
    · subst m; exact h1 _ (by simp)
    by_cases hmj : m = j
    · subst m; exact h1 _ (by simp)
    rcases others_exhaust i j m hij hmi hmj with hmk | hml
    · subst m; exact h1 _ (by simp)
    · subst m; exact h2 _ (by simp)
  · intro h
    exact ⟨fun m _ => h m (Finset.mem_univ _), fun m _ => h m (Finset.mem_univ _)⟩

private theorem sliver_patch_valuation_of_cover_ae (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (i j : Fin 4)
    (hij : i ≠ j) (hcom : isCommon c i j)
    (hCover : body c {i,j,oth1 i j} ∪ body c {i,j,oth2 i j} = body c {i,j})
    (hAbsent1 : body c {i,j,oth1 i j} =ᵐ[sphereMeasure (c (oth1 i j))] body c Finset.univ)
    (hAbsent2 : body c {i,j,oth2 i j} =ᵐ[sphereMeasure (c (oth2 i j))] body c Finset.univ)
    (m : Fin 4) :
    pArea c m Finset.univ = pArea c m {i,j,oth1 i j} + pArea c m {i,j,oth2 i j} - pArea c m {i,j} ∧
    pMoment c m Finset.univ = pMoment c m {i,j,oth1 i j} + pMoment c m {i,j,oth2 i j} - pMoment c m {i,j} := by
  by_cases hm : m = i ∨ m = j
  · exact sliver_common_patch_valuation c i j m hm hCover (pair_bodies_inter c i j hij)
      (body_integrable c m _ ⟨i, by simp⟩) (body_integrable c m _ ⟨i, by simp⟩)
  have hmi : m ≠ i := fun h => hm (Or.inl h)
  have hmj : m ≠ j := fun h => hm (Or.inr h)
  obtain ⟨hki,hkj,hli,hlj,hkl⟩ := others_distinct i j hij
  rcases others_exhaust i j m hij hmi hmj with hmk | hml
  · subst m
    have hA := congrArg ENNReal.toReal (measure_congr hAbsent1)
    have hM := setIntegral_congr_set (f := fun x => x-c (oth1 i j)) hAbsent1
    simpa [pArea,pMoment,hki,hkj,hkl, hA,hM] using And.intro hA.symm hM.symm
  · subst m
    have hA := congrArg ENNReal.toReal (measure_congr hAbsent2)
    have hM := setIntegral_congr_set (f := fun x => x-c (oth2 i j)) hAbsent2
    simpa [pArea,pMoment,hli,hlj,hkl.symm,hA,hM] using And.intro hA.symm hM.symm

private def Cov_SphereNullAPI : Prop :=
  ∀ x y : Pt, x ≠ y → sphereMeasure x (Metric.sphere y 1) = 0

private theorem Cov_lens_union_of_cover (x y z w : Pt)
    (hcover : Metric.closedBall x 1 ∩ Metric.closedBall y 1 ⊆
      Metric.closedBall z 1 ∪ Metric.closedBall w 1) :
    Metric.closedBall x 1 ∩ Metric.closedBall y 1 =
      ((Metric.closedBall x 1 ∩ Metric.closedBall y 1) ∩ Metric.closedBall z 1) ∪
      ((Metric.closedBall x 1 ∩ Metric.closedBall y 1) ∩ Metric.closedBall w 1) := by
  apply Set.Subset.antisymm
  · intro p hp
    rcases hcover hp with hz | hw
    · exact Or.inl ⟨hp, hz⟩
    · exact Or.inr ⟨hp, hw⟩
  · intro p hp
    rcases hp with hp | hp <;> exact hp.1

private theorem Cov_sphere_interior_mem_other (L : Set Pt) (z w p : Pt)
    (hcover : L ⊆ Metric.closedBall z 1 ∪ Metric.closedBall w 1)
    (hp : p ∈ interior L) (hs : p ∈ Metric.sphere z 1) :
    p ∈ Metric.closedBall w 1 := by
  by_contra hw
  let U : Set Pt := interior L ∩ (Metric.closedBall w 1)ᶜ
  have ho : IsOpen U := isOpen_interior.inter Metric.isClosed_closedBall.isOpen_compl
  have hup : p ∈ U := ⟨hp, hw⟩
  have hu : U ⊆ Metric.closedBall z 1 := by
    intro q hq
    rcases hcover (interior_subset hq.1) with hz | hw'
    · exact hz
    · exact (hq.2 hw').elim
  have hi : p ∈ interior (Metric.closedBall z 1) := interior_maximal hu ho hup
  rw [interior_closedBall z (by norm_num : (1 : ℝ) ≠ 0)] at hi
  have he : dist p z = 1 := hs
  have hl : dist p z < 1 := hi
  linarith

private theorem Cov_sphere_ae (z : Pt) : ∀ᵐ p ∂sphereMeasure z, p ∈ Metric.sphere z 1 := by
  have hunit : ∀ᵐ p ∂sphereMeasure z, ‖p - z‖ = 1 := by
    change ∀ᵐ p ∂SphereGeom.sphereMeasure z, ‖p - z‖ = 1
    rw [SphereGeom.sphereMeasure, ae_map_iff]
    · filter_upwards with u
      simpa [add_sub_cancel_left, Metric.mem_sphere, dist_zero_right] using u.property
    · fun_prop
    · exact isClosed_eq (by fun_prop) continuous_const |>.measurableSet
  filter_upwards [hunit] with p hp
  simpa [Metric.mem_sphere, dist_eq_norm] using hp

private theorem Cov_triple_body_ae (nullAPI : Cov_SphereNullAPI) (x y z w : Pt)
    (hzx : z ≠ x) (hzy : z ≠ y)
    (hcover : Metric.closedBall x 1 ∩ Metric.closedBall y 1 ⊆
      Metric.closedBall z 1 ∪ Metric.closedBall w 1) :
    (((Metric.closedBall x 1 ∩ Metric.closedBall y 1) ∩ Metric.closedBall z 1) : Set Pt)
      =ᵐ[sphereMeasure z]
    ((((Metric.closedBall x 1 ∩ Metric.closedBall y 1) ∩ Metric.closedBall z 1) ∩
      Metric.closedBall w 1) : Set Pt) := by
  have hax : ∀ᵐ p ∂sphereMeasure z, p ∉ Metric.sphere x 1 := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using nullAPI z x hzx
  have hay : ∀ᵐ p ∂sphereMeasure z, p ∉ Metric.sphere y 1 := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using nullAPI z y hzy
  apply Filter.eventuallyEq_set.2
  filter_upwards [Cov_sphere_ae z, hax, hay] with p hs hpx hpy
  constructor
  · intro htr
    have hxle : dist p x ≤ 1 := htr.1.1
    have hyle : dist p y ≤ 1 := htr.1.2
    have hxne : dist p x ≠ 1 := hpx
    have hyne : dist p y ≠ 1 := hpy
    have hxlt : dist p x < 1 := by
      rcases hxle.lt_or_eq with h | h
      · exact h
      · exact (hxne h).elim
    have hylt : dist p y < 1 := by
      rcases hyle.lt_or_eq with h | h
      · exact h
      · exact (hyne h).elim
    have hInt : p ∈ interior (Metric.closedBall x 1 ∩ Metric.closedBall y 1) := by
      rw [interior_inter, interior_closedBall x (by norm_num : (1 : ℝ) ≠ 0),
        interior_closedBall y (by norm_num : (1 : ℝ) ≠ 0)]
      exact ⟨hxlt, hylt⟩
    exact ⟨htr, Cov_sphere_interior_mem_other _ z w p hcover hInt hs⟩
  · exact fun h => h.1

private theorem Cov_Kset_four (c : Fin 4 → Pt) (i j k l : Fin 4)
    (hlabels : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ) :
    Kset c = ((Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1) ∩
      Metric.closedBall (c k) 1) ∩ Metric.closedBall (c l) 1 := by
  rw [Kset, ← hlabels]
  ext p
  simp [body, and_assoc]

private theorem Cov_body_pair (c : Fin 4 → Pt) (i j : Fin 4) :
    body c {i, j} = Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1 := by
  ext p
  simp [body]

private theorem Cov_body_triple (c : Fin 4 → Pt) (i j k : Fin 4) :
    body c {i, j, k} =
      (Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1) ∩ Metric.closedBall (c k) 1 := by
  ext p
  simp [body, and_assoc]

private theorem path_centres_ne (hc : IsPathConfig c X Y s) (i j : Fin 4) (hij : i ≠ j) :
    c i ≠ c j := by
  intro he
  obtain ⟨hki,hkj,-⟩ := others_distinct i j hij
  have hQ := path_Q_pos hc i j (oth1 i j) hij hki.symm hkj.symm
  simp [Qf, QT, DeltaT, q, he] at hQ

private theorem path_four_labels (i j : Fin 4) (hij : i ≠ j) :
    ({i,j,oth1 i j,oth2 i j} : Finset (Fin 4)) = Finset.univ := by
  fin_cases i <;> fin_cases j <;> norm_num [oth1,oth2] at * <;> decide

private theorem absent_bodies_ae_from_cover (hc : IsPathConfig c X Y s) (i j : Fin 4)
    (hij : i ≠ j)
    (hCover : body c {i,j,oth1 i j} ∪ body c {i,j,oth2 i j} = body c {i,j}) :
    (body c {i,j,oth1 i j} =ᵐ[sphereMeasure (c (oth1 i j))] body c Finset.univ) ∧
    (body c {i,j,oth2 i j} =ᵐ[sphereMeasure (c (oth2 i j))] body c Finset.univ) := by
  have hsub : Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1 ⊆
      Metric.closedBall (c (oth1 i j)) 1 ∪ Metric.closedBall (c (oth2 i j)) 1 := by
    intro x hx
    have hp : x ∈ body c {i,j} := by rwa [body_pair]
    rw [← hCover] at hp
    rcases hp with hp | hp
    · exact Or.inl ((mem_body c _ x).mp hp _ (by simp))
    · exact Or.inr ((mem_body c _ x).mp hp _ (by simp))
  have hsub' : Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1 ⊆
      Metric.closedBall (c (oth2 i j)) 1 ∪ Metric.closedBall (c (oth1 i j)) 1 := by
    simpa only [Set.union_comm] using hsub
  obtain ⟨hki,hkj,hli,hlj,hkl⟩ := others_distinct i j hij
  have labels := path_four_labels i j hij
  have labels' : ({i,j,oth2 i j,oth1 i j} : Finset (Fin 4)) = Finset.univ := by
    calc
      ({i,j,oth2 i j,oth1 i j} : Finset (Fin 4)) = {i,j,oth1 i j,oth2 i j} := by
        ext m
        simp only [Finset.mem_insert,Finset.mem_singleton]
        tauto
      _ = Finset.univ := labels
  have hnull : Cov_SphereNullAPI := SolidGeom.sphereMeasure_sphere_inter_null
  constructor
  · change (body c {i,j,oth1 i j}) =ᵐ[sphereMeasure (c (oth1 i j))] Kset c
    rw [Cov_body_triple, Cov_Kset_four c i j (oth1 i j) (oth2 i j) labels]
    exact Cov_triple_body_ae hnull _ _ _ _ (path_centres_ne hc _ _ hki)
      (path_centres_ne hc _ _ hkj) hsub
  · change (body c {i,j,oth2 i j}) =ᵐ[sphereMeasure (c (oth2 i j))] Kset c
    rw [Cov_body_triple, Cov_Kset_four c i j (oth2 i j) (oth1 i j) labels']
    exact Cov_triple_body_ae hnull _ _ _ _ (path_centres_ne hc _ _ hli)
      (path_centres_ne hc _ _ hlj) hsub'

private theorem sliver_patch_valuation_from_cover (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0)
    (i j : Fin 4) (hij : i ≠ j) (hcom : isCommon c i j)
    (hCover : body c {i,j,oth1 i j} ∪ body c {i,j,oth2 i j} = body c {i,j}) (m : Fin 4) :
    pArea c m Finset.univ = pArea c m {i,j,oth1 i j} + pArea c m {i,j,oth2 i j} - pArea c m {i,j} ∧
    pMoment c m Finset.univ = pMoment c m {i,j,oth1 i j} + pMoment c m {i,j,oth2 i j} - pMoment c m {i,j} := by
  obtain ⟨hA1,hA2⟩ := absent_bodies_ae_from_cover hc i j hij hCover
  exact sliver_patch_valuation_of_cover_ae hc hP i j hij hcom hCover hA1 hA2 m

private theorem sliver_patch_valuation_from_subcover (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0)
    (i j : Fin 4) (hij : i ≠ j) (hcom : isCommon c i j)
    (hcover : body c {i,j} ⊆ Metric.closedBall (c (oth1 i j)) 1 ∪ Metric.closedBall (c (oth2 i j)) 1)
    (m : Fin 4) :
    pArea c m Finset.univ = pArea c m {i,j,oth1 i j} + pArea c m {i,j,oth2 i j} - pArea c m {i,j} ∧
    pMoment c m Finset.univ = pMoment c m {i,j,oth1 i j} + pMoment c m {i,j,oth2 i j} - pMoment c m {i,j} := by
  have hunion := Cov_lens_union_of_cover (c i) (c j) (c (oth1 i j)) (c (oth2 i j))
    (by simpa only [body_pair] using hcover)
  have hU : body c {i,j,oth1 i j} ∪ body c {i,j,oth2 i j} = body c {i,j} := by
    rw [Cov_body_pair,Cov_body_triple,Cov_body_triple]
    exact hunion.symm
  exact sliver_patch_valuation_from_cover hc hP i j hij hcom hU m

theorem proof_HardSphereB5_Lean_Geometry_PathCore_sliver_patch_valuation {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (i j : Fin 4)
    (hij : i ≠ j) (hcom : isCommon c i j) (m : Fin 4) :
    pArea c m Finset.univ =
        pArea c m {i, j, oth1 i j} + pArea c m {i, j, oth2 i j} - pArea c m {i, j} ∧
      pMoment c m Finset.univ =
        pMoment c m {i, j, oth1 i j} + pMoment c m {i, j, oth2 i j} - pMoment c m {i, j} := by
  exact sliver_patch_valuation_from_subcover hc hP i j hij hcom (sliver_lens_covered hc hP i j hij hcom) m

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_sliver_patch_valuation
