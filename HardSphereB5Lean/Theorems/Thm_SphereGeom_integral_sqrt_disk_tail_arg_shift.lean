import HardSphereB5Lean.Proofs.Proof_SphereGeom_integral_sqrt_disk_tail_arg_shift
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SphereGeom.integral_sqrt_disk_tail_arg_shift :
    ∀ (r d h b : ℝ) (hr : 0 < r) (hh0 : -r < h - d) (hh1 : h - d < r) (hb : d + r ≤ b), (∫ t in h..b, Real.sqrt (r ^ 2 - (t - d) ^ 2)) = (r ^ 2 / 2) * Complex.arg ⟨h-d, Real.sqrt (r ^ 2 - (h - d) ^ 2)⟩ - ((h - d) / 2) * Real.sqrt (r ^ 2 - (h - d) ^ 2) :=
  @proof_SphereGeom_integral_sqrt_disk_tail_arg_shift
