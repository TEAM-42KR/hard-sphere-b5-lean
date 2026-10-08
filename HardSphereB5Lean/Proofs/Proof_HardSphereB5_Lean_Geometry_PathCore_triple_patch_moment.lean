import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SolidGeom_area_two_cap
import HardSphereB5Lean.Theorems.Thm_SolidGeom_moment_two_cap
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_pathFaceQ_pos
set_option autoImplicit false
open HardSphereB5.Lean.Geometry.PathCore HardSphereB5.Lean MeasureTheory Real
open scoped Classical

noncomputable section
open MeasureTheory Real

open HardSphereB5.Lean (Pt)
open scoped Classical

variable {c : Fin 4 → Pt} {X Y s : ℝ}

private theorem mem_body (c : Fin 4 → Pt) (F : Finset (Fin 4)) (x : Pt) :
    x ∈ body c F ↔ ∀ i ∈ F, dist x (c i) ≤ 1 := by
  simp [body, Metric.mem_closedBall]

private theorem body_triple (c : Fin 4 → Pt) (i j k : Fin 4) :
    body c {i,j,k} = Metric.closedBall (c i) 1 ∩
      (Metric.closedBall (c j) 1 ∩ Metric.closedBall (c k) 1) := by
  ext x
  simp [mem_body, Metric.mem_closedBall]

private theorem ae_closedBall (o : Pt) : ∀ᵐ x ∂sphereMeasure o, x ∈ Metric.closedBall o 1 := by
  let f : Metric.sphere (0 : Pt) 1 → Pt := fun u => o + (u : Pt)
  have hf : Measurable f := (continuous_const.add continuous_subtype_val).measurable
  change ∀ᵐ x ∂Measure.map f (volume.toSphere), x ∈ Metric.closedBall o 1
  apply (ae_map_iff hf.aemeasurable measurableSet_closedBall).mpr
  filter_upwards [] with u
  have hu : ‖(u : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using u.property
  simpa [f, Metric.mem_closedBall, dist_eq_norm, hu]

private theorem inter_closedBall_ae (o : Pt) (A : Set Pt) :
    (Metric.closedBall o 1 ∩ A : Set Pt) =ᵐ[sphereMeasure o] A := by
  filter_upwards [ae_closedBall o] with x hx
  apply propext
  change x ∈ Metric.closedBall o 1 ∩ A ↔ x ∈ A
  simp only [Set.mem_inter_iff, hx, true_and]

private theorem Qf_swap (c : Fin 4 → Pt) (i j k : Fin 4) :
    Qf c i k j = Qf c i j k := by
  unfold Qf QT DeltaT q
  rw [dist_comm (c k) (c j)]
  ring

private theorem path_Q_pos (hc : IsPathConfig c X Y s) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : 0 < Qf c i j k := by
  exact HardSphereB5.Lean.Geometry.pathFaceQ_pos c X Y s hc.q01 hc.q02 hc.q03 hc.q12 hc.q13
    hc.q23 hc.X_pos hc.X_lt_one hc.Y_pos hc.Y_lt_one hc.H_pos i j k hij hik hjk

private theorem cross_triple (v w : Pt) :
    cross (v-w) (cross v w) =
      (inner ℝ (v-w) w) • v - (inner ℝ v (v-w)) • w := by
  apply WithLp.ofLp_injective 2
  simpa only [cross, SphereGeom.cross, WithLp.ofLp_toLp, WithLp.ofLp_sub, WithLp.ofLp_smul,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    using cross_cross_eq_smul_sub_smul' (WithLp.ofLp (v-w)) (WithLp.ofLp v) (WithLp.ofLp w)

private theorem endpoint_scalar (r v w : Pt) :
    inner ℝ r (cross (v-w) (cross v w)) =
      ((‖v‖^2 - ‖w‖^2 - ‖v-w‖^2) * inner ℝ r v
        - (‖v‖^2 - ‖w‖^2 + ‖v-w‖^2) * inner ℝ r w) / 2 := by
  rw [cross_triple]
  simp only [inner_sub_right, inner_smul_right, inner_sub_left,
    real_inner_self_eq_norm_sq, norm_sub_sq_real, real_inner_comm w v]
  ring

private theorem triple_patch_area (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    pArea c i {i, j, k} =
      2 * π - 2 * gammaA c i j k - √(q c i j) * betaA c i j k - √(q c i k) * betaA c i k j := by
  have hm := measure_congr (inter_closedBall_ae (c i)
    (Metric.closedBall (c j) 1 ∩ Metric.closedBall (c k) 1))
  simp only [pArea, Finset.mem_insert, true_or, if_pos, body_triple]
  rw [hm]
  simp only [gammaA, betaA, atan2, Qf_swap]
  simpa only [sphereMeasure, q, Qf, QT, DeltaT, dist_comm]
    using SolidGeom.area_two_cap (c i) (c j) (c k) (path_Q_pos hc i j k hij hik hjk)

private theorem triple_patch_moment_s5proof (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    pMoment c i {i, j, k} =
      ((1 - q c i j / 4) / √(q c i j) * betaA c i j k) • (c j - c i)
        + ((1 - q c i k / 4) / √(q c i k) * betaA c i k j) • (c k - c i)
        + (√(Qf c i j k) / Deltaf c i j k) •
            cross ((c j - c i) - (c k - c i)) (cross (c j - c i) (c k - c i)) := by
  simp only [pMoment, Finset.mem_insert, true_or, if_pos, body_triple]
  rw [setIntegral_congr_set (inter_closedBall_ae (c i)
    (Metric.closedBall (c j) 1 ∩ Metric.closedBall (c k) 1))]
  simp only [betaA, atan2, Qf_swap]
  simpa only [sphereMeasure, cross, q, Qf, QT, DeltaT, Deltaf, dist_comm]
    using SolidGeom.moment_two_cap (c i) (c j) (c k) (path_Q_pos hc i j k hij hik hjk)

private theorem triple_patch_moment_scalar (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (cs : Pt) :
    inner ℝ (cs - c i) (pMoment c i {i, j, k}) =
      (1 - q c i j / 4) * inner ℝ (cs - c i) (c j - c i) * betaA c i j k / √(q c i j)
        + (1 - q c i k / 4) * inner ℝ (cs - c i) (c k - c i) * betaA c i k j / √(q c i k)
        + √(Qf c i j k) * ((q c i j - q c i k - q c j k) * inner ℝ (cs - c i) (c j - c i)
            - (q c i j - q c i k + q c j k) * inner ℝ (cs - c i) (c k - c i)) /
          (2 * Deltaf c i j k) := by
  rw [triple_patch_moment_s5proof hc i j k hij hik hjk]
  simp only [inner_add_right, inner_smul_right]
  rw [endpoint_scalar]
  have hv : ‖c j-c i‖^2 = q c i j := by simp [q, dist_eq_norm, norm_sub_rev]
  have hw : ‖c k-c i‖^2 = q c i k := by simp [q, dist_eq_norm, norm_sub_rev]
  have hvw : ‖(c j-c i)-(c k-c i)‖^2 = q c j k := by
    simp [q, dist_eq_norm, sub_sub_sub_cancel_right]
  rw [hv, hw, hvw]
  ring

open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_Lean_Geometry_PathCore_triple_patch_moment : ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k),
  pMoment c i {i, j, k} =
      ((1 - q c i j / 4) / √(q c i j) * betaA c i j k) • (c j - c i)
        + ((1 - q c i k / 4) / √(q c i k) * betaA c i k j) • (c k - c i)
        + (√(Qf c i j k) / Deltaf c i j k) •
            cross ((c j - c i) - (c k - c i)) (cross (c j - c i) (c k - c i)) := by
  exact @triple_patch_moment_s5proof
