import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Arrangement_unit_frame_exists
set_option autoImplicit false
open SphereGeom Module

theorem proof_SphereGeom_Aux_ConvexCone_plane_transverse_coordinates (p v : E3) (hp : ‖p‖ = 1) (hv : v ≠ 0)
    (hpv : inner ℝ p v = 0) :
    ∃ w : E3, inner ℝ p w = 0 ∧ LinearIndependent ℝ ![v,w] ∧
      ∀ x : E3, inner ℝ p x = 0 → ∃ s t : ℝ, x = s • v + t • w := by
  classical
  obtain ⟨e1, e2, he⟩ := SphereGeom.Aux.Arrangement.unit_frame_exists p hp
  let e : Fin 3 → E3 := ![e1,e2,p]
  let B : Basis (Fin 3) ℝ E3 := basisOfOrthonormalOfCardEqFinrank he (by simp [E3])
  have hrep (x : E3) : x = (B.repr x 0) • e1 + (B.repr x 1) • e2 +
      (B.repr x 2) • p := by
    have hx := B.sum_repr x
    simpa [Fin.sum_univ_three, B, e] using hx.symm
  have h11 : inner ℝ e1 e1 = 1 := by
    simpa using (orthonormal_iff_ite.mp he (0 : Fin 3) 0)
  have h12 : inner ℝ e1 e2 = 0 := by
    simpa using (orthonormal_iff_ite.mp he (0 : Fin 3) 1)
  have h1p : inner ℝ e1 p = 0 := by
    simpa using (orthonormal_iff_ite.mp he (0 : Fin 3) 2)
  have h21 : inner ℝ e2 e1 = 0 := by
    simpa using (orthonormal_iff_ite.mp he (1 : Fin 3) 0)
  have h22 : inner ℝ e2 e2 = 1 := by
    simpa using (orthonormal_iff_ite.mp he (1 : Fin 3) 1)
  have h2p : inner ℝ e2 p = 0 := by
    simpa using (orthonormal_iff_ite.mp he (1 : Fin 3) 2)
  have hp1 : inner ℝ p e1 = 0 := by
    simpa using (orthonormal_iff_ite.mp he (2 : Fin 3) 0)
  have hp2 : inner ℝ p e2 = 0 := by
    simpa using (orthonormal_iff_ite.mp he (2 : Fin 3) 1)
  have hpp : inner ℝ p p = 1 := by
    simpa using (orthonormal_iff_ite.mp he (2 : Fin 3) 2)
  have hcoord (x : E3) : inner ℝ e1 x = B.repr x 0 ∧
      inner ℝ e2 x = B.repr x 1 ∧ inner ℝ p x = B.repr x 2 := by
    constructor
    · conv_lhs => rw [hrep x]
      simp only [inner_add_right, inner_smul_right, h11, h12, h1p,
        RCLike.conj_to_real, mul_one, mul_zero, zero_add, add_zero]
    · constructor
      · conv_lhs => rw [hrep x]
        simp only [inner_add_right, inner_smul_right, h21, h22, h2p,
          RCLike.conj_to_real, mul_one, mul_zero, zero_add, add_zero]
      · conv_lhs => rw [hrep x]
        simp only [inner_add_right, inner_smul_right, hp1, hp2, hpp,
          RCLike.conj_to_real, mul_one, mul_zero, zero_add, add_zero]
  have hplane (x : E3) (hx : inner ℝ p x = 0) :
      x = inner ℝ e1 x • e1 + inner ℝ e2 x • e2 := by
    have h2 : B.repr x 2 = 0 := (hcoord x).2.2.symm.trans hx
    simpa [h2, ← (hcoord x).1, ← (hcoord x).2.1] using hrep x
  have h1ne : e1 ≠ 0 := by
    intro h
    simp [h] at h11
  have h2ne : e2 ≠ 0 := by
    intro h
    simp [h] at h22
  by_cases hv2 : inner ℝ e2 v = 0
  · have hv1 : inner ℝ e1 v ≠ 0 := by
      intro hv1
      apply hv
      simpa [hv1, hv2] using hplane v hpv
    refine ⟨e2, hp2, ?_, ?_⟩
    · apply linearIndependent_fin2.mpr
      refine ⟨h2ne, ?_⟩
      intro s heq
      have hi := congrArg (fun x => inner ℝ e1 x) heq
      simp [inner_smul_right, h12] at hi
      exact hv1 hi.symm
    · intro x hx
      refine ⟨inner ℝ e1 x / inner ℝ e1 v, inner ℝ e2 x, ?_⟩
      rw [hplane v hpv]
      simp only [hv2, zero_smul, add_zero, smul_smul, inner_smul_right, h11,
        mul_one, div_mul_cancel₀ _ hv1]
      exact hplane x hx
  · refine ⟨e1, hp1, ?_, ?_⟩
    · apply linearIndependent_fin2.mpr
      refine ⟨h1ne, ?_⟩
      intro s heq
      have hi := congrArg (fun x => inner ℝ e2 x) heq
      simp [inner_smul_right, h21] at hi
      exact hv2 hi.symm
    · intro x hx
      refine ⟨inner ℝ e2 x / inner ℝ e2 v,
        inner ℝ e1 x - (inner ℝ e2 x / inner ℝ e2 v) * inner ℝ e1 v, ?_⟩
      rw [hplane x hx, hplane v hpv]
      simp only [inner_add_right, inner_smul_right, h11, h12, h21, h22,
        RCLike.conj_to_real, mul_one, mul_zero, zero_add, add_zero,
        smul_add, smul_smul, div_mul_cancel₀ _ hv2]
      module
