import HardSphereB5Lean.Proofs.Proof_SphereGeom_twoCap_polar_azimuth_slice
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.twoCap_polar_azimuth_slice :
    ∀ (e : Fin 3 → E3) (he : Orthonormal ℝ e)
    (k l alpha theta : ℝ) (hk : 0 < k) (hl : 0 < l)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ Real.pi) (ht0 : 0 < theta) (ht1 : theta < Real.pi),
    let f := Real.arccos (k / Real.sqrt (1 - Real.cos theta ^ 2))
    let g := Real.arccos (l / Real.sqrt (1 - Real.cos theta ^ 2))
    (∫ phi in (0 : ℝ)..(2 * Real.pi),
      (cap (e 0) k ∩ cap (Real.cos alpha • e 0 + Real.sin alpha • e 1) l).indicator
      (fun _ : E3 => (1 : ℝ))
      ((Real.sin theta * Real.cos phi) • e 0 + (Real.sin theta * Real.sin phi) • e 1 +
        Real.cos theta • e 2)) =
      max 0 (min (2 * f) (min (2 * g) (f + g - alpha))) :=
  @proof_SphereGeom_twoCap_polar_azimuth_slice
