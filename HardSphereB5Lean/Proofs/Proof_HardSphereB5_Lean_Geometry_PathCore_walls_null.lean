import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section

private theorem S5b_PolyNull_quadraticZerosFinite (a b c : ℝ) (ha : a ≠ 0) :
    Set.Finite {t : ℝ | a * t ^ 2 + b * t + c = 0} := by
  classical
  let p : Polynomial ℝ := Polynomial.C a * Polynomial.X ^ 2 +
    Polynomial.C b * Polynomial.X + Polynomial.C c
  have hp : p ≠ 0 := by
    intro hp
    have hc := congrArg (fun q : Polynomial ℝ => q.coeff 2) hp
    apply ha
    simpa [p] using hc
  simpa [p, Polynomial.IsRoot] using Polynomial.finite_setOfPred_isRoot hp

end

section

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_walls_null_of_deps : volume wallSet = 0 := by
  classical

  have hlast (S : Set (ℝ × ℝ × ℝ)) (hS : MeasurableSet S)
      (hfinite : ∀ x y : ℝ, Set.Finite {z : ℝ | (x, y, z) ∈ S}) : volume S = 0 := by
    change ((volume : Measure ℝ).prod
      ((volume : Measure ℝ).prod (volume : Measure ℝ))) S = 0
    refine Measure.measure_prod_null_of_ae_null hS (Filter.Eventually.of_forall ?_)
    intro x
    change ((volume : Measure ℝ).prod (volume : Measure ℝ))
      {p : ℝ × ℝ | (x, p) ∈ S} = 0
    refine Measure.measure_prod_null_of_ae_null
      (hS.preimage (measurable_const.prodMk measurable_id))
      (Filter.Eventually.of_forall ?_)
    intro y
    change volume {z : ℝ | (x, y, z) ∈ S} = 0
    exact (hfinite x y).measure_zero volume

  have hquad (f : ℝ × ℝ × ℝ → ℝ) (hf : Continuous f)
      (a : ℝ) (ha : a ≠ 0) (b c : ℝ → ℝ → ℝ)
      (hform : ∀ x y z : ℝ, f (x, y, z) = a * z ^ 2 + b x y * z + c x y) :
      volume {v : ℝ × ℝ × ℝ | f v = 0} = 0 := by
    apply hlast _ (measurableSet_eq_fun hf.measurable measurable_const)
    intro x y
    simpa only [Set.mem_setOf_eq, hform] using
      S5b_PolyNull_quadraticZerosFinite a (b x y) (c x y) ha

  have hgraph (g : ℝ → ℝ → ℝ)
      (hg : Continuous (fun v : ℝ × ℝ × ℝ => g v.1 v.2.1)) :
      volume {v : ℝ × ℝ × ℝ | v.2.2 = g v.1 v.2.1} = 0 := by
    apply hlast _ (measurableSet_eq_fun (measurable_snd.snd) hg.measurable)
    intro x y
    simpa using (Set.finite_singleton (g x y))

  have hpairFirst (a : ℝ) : volume {p : ℝ × ℝ | p.1 = a} = 0 := by
    have hs : {p : ℝ × ℝ | p.1 = a} = ({a} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp
    rw [hs, Measure.volume_eq_prod, Measure.prod_prod]
    simp

  have hfirst (a : ℝ) : volume {v : ℝ × ℝ × ℝ | v.1 = a} = 0 := by
    have hs : {v : ℝ × ℝ × ℝ | v.1 = a} =
        ({a} : Set ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
      ext v
      simp
    rw [hs, Measure.volume_eq_prod, Measure.prod_prod]
    simp

  have hsecond (a : ℝ) : volume {v : ℝ × ℝ × ℝ | v.2.1 = a} = 0 := by
    change ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)))
      {v : ℝ × ℝ × ℝ | v.2.1 = a} = 0
    apply Measure.measure_prod_null_of_ae_null
      ((measurable_fst.comp measurable_snd) (measurableSet_singleton a))
    exact Filter.Eventually.of_forall fun _ => hpairFirst a

  have hdiag : volume {v : ℝ × ℝ × ℝ | v.1 = v.2.1} = 0 := by
    change ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)))
      {v : ℝ × ℝ × ℝ | v.1 = v.2.1} = 0
    apply Measure.measure_prod_null_of_ae_null
      (measurableSet_eq_fun measurable_fst (measurable_fst.comp measurable_snd))
    refine Filter.Eventually.of_forall ?_
    intro x
    change volume {p : ℝ × ℝ | x = p.1} = 0
    simpa only [eq_comm] using hpairFirst x

  have hP : volume {v : ℝ × ℝ × ℝ | P4poly v.1 v.2.1 v.2.2 = 0} = 0 := by
    apply hquad (fun v => P4poly v.1 v.2.1 v.2.2)
      (by unfold P4poly; fun_prop) (-3) (by norm_num)
      (fun x y => 2 * x * y + 6)
      (fun x y => x ^ 2 * y ^ 2 - 4 * x ^ 2 * y - 4 * x * y ^ 2 + 10 * x * y - 3)
    intro x y z
    dsimp [P4poly]
    ring

  have hQ0 : volume {v : ℝ × ℝ × ℝ |
      -v.1 ^ 2 + v.1 * v.2.2 + 2 * v.1 - v.2.2 ^ 2 + 2 * v.2.2 - 1 = 0} = 0 := by
    apply hquad _ (by fun_prop) (-1) (by norm_num)
      (fun x _ => x + 2) (fun x _ => -x ^ 2 + 2 * x - 1)
    intro x y z
    dsimp
    ring

  have hQ1 : volume {v : ℝ × ℝ × ℝ |
      -v.2.1 ^ 2 + v.2.1 * v.2.2 + 2 * v.2.1 - v.2.2 ^ 2 + 2 * v.2.2 - 1 = 0} = 0 := by
    apply hquad _ (by fun_prop) (-1) (by norm_num)
      (fun _ y => y + 2) (fun _ y => -y ^ 2 + 2 * y - 1)
    intro x y z
    dsimp
    ring

  have hA0 : volume {v : ℝ × ℝ × ℝ |
      -v.1 ^ 2 * v.2.1 + v.1 * v.2.1 * v.2.2 + v.1 * v.2.1 - v.1 * v.2.2 +
        v.1 - v.2.2 ^ 2 + 2 * v.2.2 - 1 = 0} = 0 := by
    apply hquad _ (by fun_prop) (-1) (by norm_num)
      (fun x y => x * y - x + 2) (fun x y => -x ^ 2 * y + x * y + x - 1)
    intro x y z
    dsimp
    ring

  have hA1 : volume {v : ℝ × ℝ × ℝ |
      -v.1 * v.2.1 ^ 2 + v.1 * v.2.1 * v.2.2 + v.1 * v.2.1 - v.2.1 * v.2.2 +
        v.2.1 - v.2.2 ^ 2 + 2 * v.2.2 - 1 = 0} = 0 := by
    apply hquad _ (by fun_prop) (-1) (by norm_num)
      (fun x y => x * y - y + 2) (fun x y => -x * y ^ 2 + x * y + y - 1)
    intro x y z
    dsimp
    ring

  have hS : volume {v : ℝ × ℝ × ℝ | v.2.2 = 1} = 0 :=
    hgraph (fun _ _ => 1) (by fun_prop)
  have hG2 : volume {v : ℝ × ℝ × ℝ |
      v.2.2 = v.1 * v.2.1 - 2 * v.1 + 1} = 0 :=
    hgraph (fun x y => x * y - 2 * x + 1) (by fun_prop)
  have hG3 : volume {v : ℝ × ℝ × ℝ |
      v.2.2 = v.1 * v.2.1 - 2 * v.2.1 + 1} = 0 :=
    hgraph (fun x y => x * y - 2 * y + 1) (by fun_prop)

  have hSelector : volume {v : ℝ × ℝ × ℝ | v.2.2 = s0 v.2.1} = 0 :=
    hgraph (fun _ y => s0 y) (by unfold s0; fun_prop)

  have hAE {p : ℝ × ℝ × ℝ → Prop}
      (hn : volume {v : ℝ × ℝ × ℝ | p v} = 0) :
      ∀ᵐ v ∂(volume : Measure (ℝ × ℝ × ℝ)), ¬p v := by
    rw [ae_iff]
    simpa only [not_not] using hn

  have hall : ∀ᵐ v ∂(volume : Measure (ℝ × ℝ × ℝ)),
      ¬(P4poly v.1 v.2.1 v.2.2 = 0 ∨ v.1 = v.2.1 ∨ v.2.2 = 1 ∨
        v.2.2 = s0 v.2.1 ∨ v.1 = 0 ∨ v.1 = 1 ∨ v.2.1 = 0 ∨ v.2.1 = 1 ∨
        ∃ l, Qpoly v.1 v.2.1 v.2.2 l = 0 ∨ Apoly v.1 v.2.1 v.2.2 l = 0) := by
    filter_upwards [hAE hP, hAE hdiag, hAE hS, hAE hQ0, hAE hQ1, hAE hA0, hAE hA1,
      hAE (hfirst 0), hAE (hfirst 3), hAE (hsecond 0), hAE (hsecond 3), hAE hG2, hAE hG3, hAE hSelector, hAE (hfirst 1), hAE (hsecond 1)]
      with v hp hd hs hq0 hq1 ha0 ha1 hx0 hx3 hy0 hy3 hg2 hg3 hsel hx1 hy1
    have hx3' : 3 - v.1 ≠ 0 := by
      intro h
      apply hx3
      linarith
    have hy3' : 3 - v.2.1 ≠ 0 := by
      intro h
      apply hy3
      linarith
    have hg2' : -v.1 * v.2.1 + 2 * v.1 + v.2.2 - 1 ≠ 0 := by
      intro h
      apply hg2
      linarith
    have hg3' : -v.1 * v.2.1 + 2 * v.2.1 + v.2.2 - 1 ≠ 0 := by
      intro h
      apply hg3
      linarith
    have hQall : ∀ l : Fin 4, Qpoly v.1 v.2.1 v.2.2 l ≠ 0 := by
      intro l
      fin_cases l
      · simpa [Qpoly] using hq0
      · simpa [Qpoly] using hq1
      · simpa [Qpoly] using mul_ne_zero hy0 hy3'
      · simpa [Qpoly] using mul_ne_zero hx0 hx3'
    have hAall : ∀ l : Fin 4, Apoly v.1 v.2.1 v.2.2 l ≠ 0 := by
      intro l
      fin_cases l
      · simpa [Apoly] using ha0
      · simpa [Apoly] using ha1
      · simpa [Apoly] using mul_ne_zero hy0 hg2'
      · simpa [Apoly] using mul_ne_zero hx0 hg3'
    intro hv
    rcases hv with h | h | h | h | h | h | h | h | ⟨l, h | h⟩
    · exact hp h
    · exact hd h
    · exact hs h
    · exact hsel h
    · exact hx0 h
    · exact hx1 h
    · exact hy0 h
    · exact hy1 h
    · exact hQall l h
    · exact hAall l h
  simpa only [wallSet, ae_iff, not_not] using hall

end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_walls_null : volume wallSet = 0 := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_walls_null_of_deps

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_walls_null
