import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SolidGeom_ballInter_affine_slice_flux
set_option autoImplicit false
open MeasureTheory Real SphereGeom
set_option maxHeartbeats 1600000
private lemma g2_unit (c : E3) : ∀ᵐ x ∂sphereMeasure c, ‖x - c‖ = 1 := by
  rw [sphereMeasure, ae_map_iff]
  · filter_upwards with u
    simpa [add_sub_cancel_left, Metric.mem_sphere, dist_zero_right] using u.property
  · fun_prop
  · exact isClosed_eq (by fun_prop) continuous_const |>.measurableSet
private lemma g2_integrable (c : E3) : Integrable (fun x : E3 => x - c) (sphereMeasure c) := by
  letI : IsFiniteMeasure (sphereMeasure c) := by dsimp [sphereMeasure]; infer_instance
  exact (integrable_const (1 : ℝ)).mono' (by fun_prop) ((g2_unit c).mono fun x hx => hx.le)
private lemma g2_frame (k : Fin 3) : Orthonormal ℝ
    (fun i : Fin 3 => (EuclideanSpace.basisFun (Fin 3) ℝ) (Equiv.swap 2 k i)) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.comp (Equiv.swap 2 k) (Equiv.swap 2 k).injective

private lemma g2_flux_expand (c o : E3) (A : Set E3) :
    (∫ x in A, inner ℝ (x - o) (x - c) ∂sphereMeasure c) =
      (sphereMeasure c A).toReal + inner ℝ (c - o) (∫ x in A, (x - c) ∂sphereMeasure c) := by
  letI : IsFiniteMeasure (sphereMeasure c) := by dsimp [sphereMeasure]; infer_instance
  have hunit : ∀ᵐ x ∂sphereMeasure c, ‖x - c‖ = 1 := by
    rw [sphereMeasure, ae_map_iff]
    · filter_upwards with u
      simpa [add_sub_cancel_left, Metric.mem_sphere, dist_zero_right] using u.property
    · fun_prop
    · exact isClosed_eq (by fun_prop) continuous_const |>.measurableSet
  have hi : Integrable (fun x : E3 => x - c) (sphereMeasure c) :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop) (hunit.mono fun x hx => hx.le)
  have hia := hi.integrableOn (s := A)
  have heq : (fun x : E3 => inner ℝ (x - o) (x - c)) =ᵐ[(sphereMeasure c).restrict A]
      (fun x => (1 : ℝ) + inner ℝ (c - o) (x - c)) := by
    filter_upwards [ae_restrict_of_ae hunit] with x hx
    have hv : x - o = (x - c) + (c - o) := by abel
    rw [hv, inner_add_left, real_inner_self_eq_norm_sq, hx]
    ring
  rw [integral_congr_ae heq, integral_add (integrable_const _) (hia.const_inner _),
    integral_const, integral_inner hia]
  simp [Measure.real]

private lemma g2_axis_integrable (c : E3) (k : Fin 3) :
    Integrable (fun x : E3 => inner ℝ ((EuclideanSpace.basisFun (Fin 3) ℝ) k) x *
      inner ℝ ((EuclideanSpace.basisFun (Fin 3) ℝ) k) (x - c)) (sphereMeasure c) := by
  let v := (EuclideanSpace.basisFun (Fin 3) ℝ) k
  letI : IsFiniteMeasure (sphereMeasure c) := by dsimp [sphereMeasure]; infer_instance
  have hv : ‖v‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one k
  apply (integrable_const (‖c‖ + 1)).mono' (by fun_prop)
  filter_upwards [g2_unit c] with x hx
  have hxnorm : ‖x‖ ≤ ‖c‖ + 1 := by
    calc ‖x‖ = ‖c + (x - c)‖ := by congr 1; abel
         _ ≤ ‖c‖ + ‖x - c‖ := norm_add_le _ _
         _ = _ := by rw [hx]
  rw [norm_mul]
  calc
    _ ≤ (‖v‖ * ‖x‖) * (‖v‖ * ‖x - c‖) :=
      mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _) (by positivity)
    _ = ‖x‖ := by rw [hv, hx]; ring
    _ ≤ ‖c‖ + 1 := hxnorm

theorem proof_SolidGeom_volume_ballInter_divergence_inj (n : ℕ) (c : Fin n → E3) (hc : Function.Injective c)
    (hK : (interior (⋂ i, Metric.closedBall (c i) 1)).Nonempty) :
    3 * (volume (⋂ i, Metric.closedBall (c i) 1)).toReal =
      ∑ i, ((sphereMeasure (c i) (⋂ j, Metric.closedBall (c j) 1)).toReal
        + inner ℝ (c i) (∫ x in ⋂ j, Metric.closedBall (c j) 1, (x - c i) ∂(sphereMeasure (c i)))) := by
  let K := ⋂ j, Metric.closedBall (c j) 1
  have haxis (k : Fin 3) :
      ∑ i, ∫ x in K, inner ℝ ((EuclideanSpace.basisFun (Fin 3) ℝ) k) x *
        inner ℝ ((EuclideanSpace.basisFun (Fin 3) ℝ) k) (x - c i) ∂sphereMeasure (c i) =
        (volume K).toReal := by
    have hf := SolidGeom.ballInter_affine_slice_flux n c hc hK
      (fun i => (EuclideanSpace.basisFun (Fin 3) ℝ) (Equiv.swap 2 k i)) (g2_frame k) 0 1
    simpa only [Equiv.swap_apply_left, one_mul, zero_add] using hf
  have htotal : ∑ i, ∫ x in K, inner ℝ x (x - c i) ∂sphereMeasure (c i) =
      3 * (volume K).toReal := by
    calc
      _ = ∑ i, ∑ k : Fin 3, ∫ x in K,
          inner ℝ ((EuclideanSpace.basisFun (Fin 3) ℝ) k) x *
          inner ℝ ((EuclideanSpace.basisFun (Fin 3) ℝ) k) (x - c i) ∂sphereMeasure (c i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← integral_finset_sum]
        · apply integral_congr_ae
          filter_upwards with x
          simpa only [real_inner_comm x] using
            ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_inner_mul_inner x (x - c i)).symm
        · intro k hk
          exact (g2_axis_integrable (c i) k).integrableOn
      _ = ∑ k : Fin 3, ∑ i, ∫ x in K,
          inner ℝ ((EuclideanSpace.basisFun (Fin 3) ℝ) k) x *
          inner ℝ ((EuclideanSpace.basisFun (Fin 3) ℝ) k) (x - c i) ∂sphereMeasure (c i) :=
        Finset.sum_comm
      _ = _ := by simp only [haxis, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  change 3 * (volume K).toReal = _
  rw [← htotal]
  apply Finset.sum_congr rfl
  intro i hi
  simpa using g2_flux_expand (c i) 0 K
