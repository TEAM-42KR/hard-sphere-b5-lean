import HardSphereB5Lean.Proofs.Proof_SphereGeom_two_cap_frame_moment_closed
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem SphereGeom.two_cap_frame_moment_closed :
    ∀ (e : Fin 3 → E3) (he : Orthonormal ℝ e) (A K L : ℝ) (hA0 : 0 < A) (hA2 : A < 2) (hL : 0 < L) (hB2 : K ^ 2 + L ^ 2 < 4) (hH : 0 < L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2),
    let B := Real.sqrt (K ^ 2 + L ^ 2)
 let H := L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2
 (∫ u in cap (A • e 0) (A ^ 2 / 2) ∩ cap (K • e 0 + L • e 1) ((K ^ 2 + L ^ 2) / 2), u ∂dOmega) =
 (((1 - A ^ 2 / 4) * Complex.arg ⟨B ^ 2 - A * K, 2 * Real.sqrt H⟩ + ((1 - B ^ 2 / 4) * K / B) * Complex.arg ⟨B * (A - K), 2 * Real.sqrt H⟩ - Real.sqrt H / 2)) • e 0 +
 ((((1 - B ^ 2 / 4) * L / B) * Complex.arg ⟨B * (A - K), 2 * Real.sqrt H⟩ - Real.sqrt H * (A - K) / (2 * L))) • e 1 :=
  @proof_SphereGeom_two_cap_frame_moment_closed
