import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 600000

theorem proof_HardSphereB5_SphericalCrofton_Aux_frontierSigma_subset_arcs (D : Pt) :
    sFrontier (SigmaD D) ⊆ arcA D ∪ arcB D := by
  let S := Metric.sphere (0 : Pt) 1
  let A : Set S := {y | ‖D + (y : Pt)‖ ≤ 1}
  let B : Set S := {y | dist (D + (y : Pt)) e ≤ 1}
  have hu (y : S) : ‖(y : Pt)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using y.property
  have hA : IsClosed A := isClosed_le (by fun_prop) continuous_const
  have hB : IsClosed B := isClosed_le (by fun_prop) continuous_const
  have hset : (Subtype.val : S → Pt) ⁻¹' SigmaD D = A ∩ B := by
    ext y
    simp [SigmaD, LamC, A, B, hu y, Metric.mem_closedBall, dist_zero_right]
  rintro u ⟨y,hy,rfl⟩
  change y ∈ frontier ((Subtype.val : S → Pt) ⁻¹' SigmaD D) at hy
  rw [hset] at hy
  have hyAB : y ∈ A ∩ B := (hA.inter hB).frontier_subset hy
  have hyS : (y : Pt) ∈ SigmaD D := by
    change y ∈ (Subtype.val : S → Pt) ⁻¹' SigmaD D
    rw [hset]
    exact hyAB
  rcases frontier_inter_subset A B hy with hyA | hyB
  · by_cases h0 : D = 0
    · have hAu : A = Set.univ := by ext z; simp [A, h0, hu z]
      have hfalse := hyA.1
      simp [hAu] at hfalse
    · apply Or.inl
      simp only [arcA, if_neg h0, Set.mem_setOf_eq]
      refine ⟨hyS, ?_⟩
      exact frontier_le_subset_eq (show Continuous (fun y : S => ‖D + (y : Pt)‖) by fun_prop)
        continuous_const hyA.1
  · by_cases he : D = e
    · have hBu : B = Set.univ := by
        ext z
        simp [B, he, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, hu z]
      have hfalse := hyB.2
      simp [hBu] at hfalse
    · apply Or.inr
      simp only [arcB, if_neg he, Set.mem_setOf_eq]
      refine ⟨hyS, ?_⟩
      exact frontier_le_subset_eq (show Continuous (fun y : S => dist (D + (y : Pt)) e) by fun_prop)
        continuous_const hyB.2
