import HardSphereB5Lean.Proofs.Proof_SphereGeom_twoCap_area_slice
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom MeasureTheory

theorem SphereGeom.twoCap_area_slice :
    ∀ (e : Fin 3 → E3) (he : Orthonormal ℝ e)
    (k l alpha : ℝ) (hk0 : 0 < k) (hk1 : k < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (ha0 : 0 < alpha) (ha1 : alpha < Real.pi),
    let H := min (Real.sqrt (1 - k ^ 2)) (Real.sqrt (1 - l ^ 2))
    let f := fun z : ℝ => Real.arccos (k / Real.sqrt (1 - z ^ 2))
    let g := fun z : ℝ => Real.arccos (l / Real.sqrt (1 - z ^ 2))
    (dOmega (cap (e 0) k ∩ cap (Real.cos alpha • e 0 + Real.sin alpha • e 1) l)).toReal =
      2 * (∫ z in (0 : ℝ)..H, max 0 (min (2 * f z) (min (2 * g z) (f z + g z - alpha)))) :=
  @proof_SphereGeom_twoCap_area_slice
