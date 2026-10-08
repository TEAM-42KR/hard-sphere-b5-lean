import HardSphereB5Lean.Theorems.Thm_SphereGeom_integral_dOmega_frame
set_option autoImplicit false
noncomputable section
open MeasureTheory SphereGeom

theorem proof_SphereGeom_twoCap_area_frame (e : Fin 3 → E3) (he : Orthonormal ℝ e)
 (v w : E3) (h k : ℝ)
 (hf : Integrable ((cap v h ∩ cap w k).indicator (fun _ : E3 => (1 : ℝ))) dOmega) :
 (dOmega (cap v h ∩ cap w k)).toReal =
 ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
 Real.sin θ * (cap v h ∩ cap w k).indicator (fun _ : E3 => (1 : ℝ))
 ((Real.sin θ * Real.cos φ) • e 0 + (Real.sin θ * Real.sin φ) • e 1 + Real.cos θ • e 2) := by
  have hv : MeasurableSet (cap v h) := by
    unfold cap
    exact (isClosed_eq (by fun_prop : Continuous (fun u : E3 => ‖u‖)) continuous_const).measurableSet.inter
      ((isClosed_le continuous_const (by fun_prop : Continuous (fun u : E3 => inner ℝ v u))).measurableSet)
  have hw : MeasurableSet (cap w k) := by
    unfold cap
    exact (isClosed_eq (by fun_prop : Continuous (fun u : E3 => ‖u‖)) continuous_const).measurableSet.inter
      ((isClosed_le continuous_const (by fun_prop : Continuous (fun u : E3 => inner ℝ w u))).measurableSet)
  have H := SphereGeom.integral_dOmega_frame e he
    ((cap v h ∩ cap w k).indicator (fun _ : E3 => (1 : ℝ))) hf
  calc
    (dOmega (cap v h ∩ cap w k)).toReal =
        ∫ u, (cap v h ∩ cap w k).indicator (fun _ : E3 => (1 : ℝ)) u ∂dOmega := by
      simpa [measureReal_def, smul_eq_mul] using
        (integral_indicator_const (μ := dOmega) (1 : ℝ) (hv.inter hw)).symm
    _ = _ := by simpa only [smul_eq_mul] using H
