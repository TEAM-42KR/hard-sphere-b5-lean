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

theorem proof_SolidGeom_moment_sum_ballInter_inj (n : ℕ) (c : Fin n → E3) (hc : Function.Injective c)
    (hK : (interior (⋂ i, Metric.closedBall (c i) 1)).Nonempty) :
    ∑ i, ∫ x in ⋂ j, Metric.closedBall (c j) 1, (x - c i) ∂(sphereMeasure (c i)) = 0 := by
  ext k
  change (∑ i, ∫ x in ⋂ j, Metric.closedBall (c j) 1, (x - c i) ∂sphereMeasure (c i)) k = 0
  rw [← EuclideanSpace.inner_basisFun_real, real_inner_comm]
  have hf := SolidGeom.ballInter_affine_slice_flux n c hc hK
    (fun i => (EuclideanSpace.basisFun (Fin 3) ℝ) (Equiv.swap 2 k i)) (g2_frame k) 1 0
  simp only [Equiv.swap_apply_left, zero_mul, add_zero, one_mul] at hf
  simp only [inner_zero_right, inner_sum]
  convert hf using 1
  apply Finset.sum_congr rfl
  intro i hi
  exact (integral_inner ((g2_integrable (c i)).integrableOn (s := ⋂ j,
    Metric.closedBall (c j) 1)) ((EuclideanSpace.basisFun (Fin 3) ℝ) k)).symm
