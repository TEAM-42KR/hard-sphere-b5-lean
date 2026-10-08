import HardSphereB5Lean.Proofs.Proof_SphereGeom_cap_positive_smul
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open SphereGeom

theorem SphereGeom.cap_positive_smul :
    ∀ (n : E3) (h d : ℝ) (hd : 0 < d), cap (d • n) (d * h) = cap n h :=
  @proof_SphereGeom_cap_positive_smul
