import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_Crofton_frame_tangent_parseval (a b g v : E3) (hframe : Orthonormal ℝ ![a, b, g])
    (hvg : inner ℝ v g = 0) :
    (inner ℝ a v) ^ 2 + (inner ℝ b v) ^ 2 = ‖v‖ ^ 2 := by
  classical
  have hspan : Submodule.span ℝ (Set.range ![a, b, g]) = ⊤ :=
    hframe.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [E3])
  let e : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk hframe hspan.ge
  have he : (e : Fin 3 → E3) = ![a, b, g] := OrthonormalBasis.coe_mk hframe hspan.ge
  have hgv : inner ℝ g v = 0 := by rw [real_inner_comm, hvg]
  have hp := e.sum_sq_inner_right v
  simpa [he, Fin.sum_univ_succ, hgv] using hp
