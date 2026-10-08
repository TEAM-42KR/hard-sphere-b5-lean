import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SolidGeom_ballInter_patch_graph_flux
import HardSphereB5Lean.Theorems.Thm_SolidGeom_ballInter_graph_ftc
set_option autoImplicit false
open MeasureTheory Real SphereGeom
theorem proof_SolidGeom_ballInter_affine_slice_flux (n : ℕ) (c : Fin n → E3) (hc : Function.Injective c)
    (hK : (interior (⋂ i, Metric.closedBall (c i) 1)).Nonempty)
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) (a b : ℝ) :
    ∑ i, ∫ x in ⋂ j, Metric.closedBall (c j) 1,
      (a + b * inner ℝ (e 2) x) * inner ℝ (e 2) (x - c i) ∂(sphereMeasure (c i)) =
      b * (volume (⋂ i, Metric.closedBall (c i) 1)).toReal := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [measure_univ_of_isAddLeftInvariant]
  · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    exact (SolidGeom.ballInter_patch_graph_flux n c e he a b).trans
      (SolidGeom.ballInter_graph_ftc n hn0 c hc hK e he a b)
