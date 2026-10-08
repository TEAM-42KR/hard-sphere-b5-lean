import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_sliver_lens_covered
import HardSphereB5Lean.Theorems.Thm_SolidGeom_volume_lens_closed
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

private theorem body_finite (c : Fin 4 → Pt) (F : Finset (Fin 4))
    (hne : F.Nonempty) : volume (body c F) ≠ ⊤ := by
  obtain ⟨i, hi⟩ := hne
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono (show body c F ⊆ Metric.closedBall (c i) 1 from
    fun x hx => (mem_body c F x).mp hx i hi))
  exact measure_closedBall_lt_top

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

private theorem sliver_volume_of_lens_cover (c : Fin 4 → Pt) (i j : Fin 4)
    (hCover : body c {i,j,oth1 i j} ∪ body c {i,j,oth2 i j} = body c {i,j})
    (hInter : body c {i,j,oth1 i j} ∩ body c {i,j,oth2 i j} = body c Finset.univ)
    (hd : dist (c i) (c j) < 2) :
    vol c Finset.univ = vol c {i,j,oth1 i j} + vol c {i,j,oth2 i j} - V2 (dist (c i) (c j)) := by
  have h := measure_inter_valuation volume
    (body c {i,j,oth1 i j}) (body c {i,j,oth2 i j})
    (body_measurable _ _) (body_finite _ _ ⟨i, by simp⟩) (body_finite _ _ ⟨i, by simp⟩)
  rw [hCover, hInter, body_pair, SolidGeom.volume_lens_closed (c i) (c j) hd.le] at h
  exact h

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

private theorem path_pair_lt_two (hc : IsPathConfig c X Y s) (i j : Fin 4) :
    dist (c i) (c j) < 2 := by
  have h01 : dist (c 0) (c 1) = 1 := by
    have h := hc.q01; unfold q at h; nlinarith [dist_nonneg (x := c 0) (y := c 1)]
  have h02 : dist (c 0) (c 2) = 1 := by
    have h := hc.q02; unfold q at h; nlinarith [dist_nonneg (x := c 0) (y := c 2)]
  have h13 : dist (c 1) (c 3) = 1 := by
    have h := hc.q13; unfold q at h; nlinarith [dist_nonneg (x := c 1) (y := c 3)]
  have h03 : dist (c 0) (c 3) < 1 := by
    have h := hc.q03; unfold q at h; nlinarith [hc.Y_lt_one, dist_nonneg (x := c 0) (y := c 3)]
  have h12 : dist (c 1) (c 2) < 1 := by
    have h := hc.q12; unfold q at h; nlinarith [hc.X_lt_one, dist_nonneg (x := c 1) (y := c 2)]
  have h23 : dist (c 2) (c 3) < 2 := by
    have h := dist_triangle (c 2) (c 1) (c 3)
    rw [dist_comm (c 2) (c 1),h13] at h
    linarith
  fin_cases i <;> fin_cases j <;> dsimp only
  · simp
  · change dist (c 0) (c 1) < 2
    rw [h01]; norm_num
  · change dist (c 0) (c 2) < 2
    rw [h02]; norm_num
  · exact h03.trans (by norm_num)
  · change dist (c 1) (c 0) < 2
    rw [dist_comm, h01]; norm_num
  · simp
  · exact h12.trans (by norm_num)
  · change dist (c 1) (c 3) < 2
    rw [h13]; norm_num
  · change dist (c 2) (c 0) < 2
    rw [dist_comm, h02]; norm_num
  · rw [dist_comm]; exact h12.trans (by norm_num)
  · simp
  · exact h23
  · rw [dist_comm]; exact h03.trans (by norm_num)
  · change dist (c 3) (c 1) < 2
    rw [dist_comm, h13]; norm_num
  · rw [dist_comm]; exact h23
  · simp

private theorem sliver_volume_from_cover (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (i j : Fin 4)
    (hij : i ≠ j) (hcom : isCommon c i j)
    (hCover : body c {i,j,oth1 i j} ∪ body c {i,j,oth2 i j} = body c {i,j}) :
    vol c Finset.univ = vol c {i,j,oth1 i j} + vol c {i,j,oth2 i j} - V2 (dist (c i) (c j)) := by
  exact sliver_volume_of_lens_cover c i j hCover (pair_bodies_inter c i j hij) (path_pair_lt_two hc i j)

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

private theorem Cov_body_pair (c : Fin 4 → Pt) (i j : Fin 4) :
    body c {i, j} = Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1 := by
  ext p
  simp [body]

private theorem Cov_body_triple (c : Fin 4 → Pt) (i j k : Fin 4) :
    body c {i, j, k} =
      (Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1) ∩ Metric.closedBall (c k) 1 := by
  ext p
  simp [body, and_assoc]

private theorem sliver_volume_from_subcover (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0)
    (i j : Fin 4) (hij : i ≠ j) (hcom : isCommon c i j)
    (hcover : body c {i,j} ⊆ Metric.closedBall (c (oth1 i j)) 1 ∪ Metric.closedBall (c (oth2 i j)) 1) :
    vol c Finset.univ = vol c {i,j,oth1 i j} + vol c {i,j,oth2 i j} - V2 (dist (c i) (c j)) := by
  have hunion := Cov_lens_union_of_cover (c i) (c j) (c (oth1 i j)) (c (oth2 i j))
    (by simpa only [body_pair] using hcover)
  have hU : body c {i,j,oth1 i j} ∪ body c {i,j,oth2 i j} = body c {i,j} := by
    rw [Cov_body_pair,Cov_body_triple,Cov_body_triple]
    exact hunion.symm
  exact sliver_volume_from_cover hc hP i j hij hcom hU

theorem proof_HardSphereB5_Lean_Geometry_PathCore_sliver_volume {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (i j : Fin 4)
    (hij : i ≠ j) (hcom : isCommon c i j) :
    vol c Finset.univ = vol c {i, j, oth1 i j} + vol c {i, j, oth2 i j} - V2 (dist (c i) (c j)) := by
  exact sliver_volume_from_subcover hc hP i j hij hcom (sliver_lens_covered hc hP i j hij hcom)

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_sliver_volume
