import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_cap_moment_transverse
import HardSphereB5Lean.Theorems.Thm_SphereGeom_two_cap_transverse_closed
set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem proof_SphereGeom_two_cap_frame_transverse_closed (e : Fin 3 → E3) (he : Orthonormal ℝ e) (A K L : ℝ) (hA0 : 0 < A) (hA2 : A < 2) (hL : 0 < L) (hB2 : K ^ 2 + L ^ 2 < 4) (hH : 0 < L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2) :
 let B := Real.sqrt (K ^ 2 + L ^ 2)
 let H := L ^ 2 * (1 - A ^ 2 / 4) - ((K ^ 2 + L ^ 2) / 2 - K * A / 2) ^ 2
 inner ℝ (e 1) (∫ u in cap (A • e 0) (A ^ 2 / 2) ∩ cap (K • e 0 + L • e 1) ((K ^ 2 + L ^ 2) / 2), u ∂dOmega) = ((1 - B ^ 2 / 4) * L / B) * Complex.arg ⟨B * (A - K), 2 * Real.sqrt H⟩ - Real.sqrt H * (A - K) / (2 * L) := by
  classical
  let f : Fin 3 → E3 := ![e 1,e 2,e 0]
  have hf : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite] at he ⊢
    have hen := (orthonormal_iff_ite.mpr he).1
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f,he,hen]
  have hc : cap (A • e 0) (A ^ 2 / 2) = cap (e 0) (A / 2) := by
    ext u
    simp only [cap,Set.mem_setOf_eq,real_inner_smul_left]
    constructor
    · rintro ⟨hn,hu⟩
      exact ⟨hn,(by nlinarith)⟩
    · rintro ⟨hn,hu⟩
      exact ⟨hn,(by nlinarith)⟩
  rw [hc]
  change inner ℝ (f 0) (∫ u in cap (f 2) (A / 2) ∩ cap (K • f 2 + L • f 0) ((K ^ 2 + L ^ 2) / 2), u ∂dOmega) = _
  rw [SphereGeom.cap_moment_transverse f hf (A / 2) K L ((K ^ 2 + L ^ 2) / 2) (by linarith) (by linarith) hL]
  exact SphereGeom.two_cap_transverse_closed A K L hA0 hA2 hL hB2 hH
