import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import Mathlib
import HardSphereB5Lean.Theorems.Thm_SolidGeom_volume_ballInter_divergence_inj
import HardSphereB5Lean.Theorems.Thm_SolidGeom_moment_sum_ballInter_inj
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open HardSphereB5.Lean.Geometry.PathCore HardSphereB5.Lean MeasureTheory Real
open scoped Classical
noncomputable section
open MeasureTheory Real

open HardSphereB5.Lean (Pt)
open scoped Classical

variable {c : Fin 4 → Pt} {X Y s : ℝ}

open HardSphereB5.Lean (Pt)
open MeasureTheory Real
open scoped Classical
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private theorem path_centers_injective (hc : IsPathConfig c X Y s) : Function.Injective c := by
  have hpos_ne {i j : Fin 4} (hp : 0 < q c i j) : c i ≠ c j := by
    intro he
    simp [q, he] at hp
  have h01 : c 0 ≠ c 1 := hpos_ne (by rw [hc.q01]; norm_num)
  have h02 : c 0 ≠ c 2 := hpos_ne (by rw [hc.q02]; norm_num)
  have h03 : c 0 ≠ c 3 := hpos_ne (by rw [hc.q03]; exact hc.Y_pos)
  have h12 : c 1 ≠ c 2 := hpos_ne (by rw [hc.q12]; exact hc.X_pos)
  have h13 : c 1 ≠ c 3 := hpos_ne (by rw [hc.q13]; norm_num)
  have h23 : c 2 ≠ c 3 := by
    intro he
    have hh : 1 = Y := hc.q02.symm.trans (by simpa [q, he] using hc.q03)
    linarith [hc.Y_lt_one]
  intro i j he
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact (h01 he).elim | exact (h01 he.symm).elim |
      exact (h02 he).elim | exact (h02 he.symm).elim |
      exact (h03 he).elim | exact (h03 he.symm).elim |
      exact (h12 he).elim | exact (h12 he.symm).elim |
      exact (h13 he).elim | exact (h13 he.symm).elim |
      exact (h23 he).elim | exact (h23 he.symm).elim

private theorem midpoint_strict (hc : IsPathConfig c X Y s) (i : Fin 4) :
    dist (midpoint ℝ (c 0) (c 1)) (c i) < 1 := by
  have h01 : dist (c 0) (c 1) ^ 2 = 1 := hc.q01
  have h02 : dist (c 0) (c 2) ^ 2 = 1 := hc.q02
  have h03 : dist (c 0) (c 3) ^ 2 = Y := hc.q03
  have h12 : dist (c 1) (c 2) ^ 2 = X := hc.q12
  have h13 : dist (c 1) (c 3) ^ 2 = 1 := hc.q13
  have hi : dist (c i) (c 0) ^ 2 + dist (c i) (c 1) ^ 2 < 2 := by
    fin_cases i
    · change dist (c 0) (c 0) ^ 2 + dist (c 0) (c 1) ^ 2 < 2
      simpa [h01] using (by norm_num : (1 : ℝ) < 2)
    · change dist (c 1) (c 0) ^ 2 + dist (c 1) (c 1) ^ 2 < 2
      simpa [dist_comm, h01] using (by norm_num : (1 : ℝ) < 2)
    · change dist (c 2) (c 0) ^ 2 + dist (c 2) (c 1) ^ 2 < 2
      simpa only [dist_comm (c 2) (c 0), dist_comm (c 2) (c 1), h02, h12] using
        (show 1 + X < 2 by linarith [hc.X_lt_one])
    · change dist (c 3) (c 0) ^ 2 + dist (c 3) (c 1) ^ 2 < 2
      simpa only [dist_comm (c 3) (c 0), dist_comm (c 3) (c 1), h03, h13] using
        (show Y + 1 < 2 by linarith [hc.Y_lt_one])
  have h := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
    (c i) (c 0) (c 1)
  rw [dist_comm (c i) (midpoint ℝ (c 0) (c 1))] at h
  nlinarith

private theorem divergence_path_s5proof (hc : IsPathConfig c X Y s) :
  3*vol c Finset.univ = ∑ i, (pArea c i Finset.univ + inner ℝ (c i) (pMoment c i Finset.univ)) ∧
  ∑ i, pMoment c i Finset.univ = 0 := by
  let U : Set Pt := ⋂ i : Fin 4, Metric.ball (c i) 1
  have hU : IsOpen U := isOpen_iInter_of_finite fun i : Fin 4 => Metric.isOpen_ball
  have hm : midpoint ℝ (c 0) (c 1) ∈ U := by
    simp only [U, Set.mem_iInter, Metric.mem_ball]
    exact midpoint_strict hc
  have hsub : U ⊆ ⋂ i : Fin 4, Metric.closedBall (c i) 1 := by
    intro x hx
    simp only [Set.mem_iInter, Metric.mem_closedBall]
    exact fun i => (Set.mem_iInter.mp hx i).le
  have hK : (interior (⋂ i : Fin 4, Metric.closedBall (c i) 1)).Nonempty :=
    ⟨_, interior_mono hsub (by rwa [hU.interior_eq])⟩
  have hinj := path_centers_injective hc
  have hvol := SolidGeom.volume_ballInter_divergence_inj 4 c hinj hK
  have hmoment := SolidGeom.moment_sum_ballInter_inj 4 c hinj hK
  constructor
  · simpa [vol, body, pArea, pMoment, sphereMeasure] using hvol
  · simpa [pMoment, body, sphereMeasure] using hmoment

open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_Lean_Geometry_PathCore_divergence_path : ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s),
  3*vol c Finset.univ = ∑ i, (pArea c i Finset.univ + inner ℝ (c i) (pMoment c i Finset.univ)) ∧
  ∑ i, pMoment c i Finset.univ = 0 := by
  exact @divergence_path_s5proof
