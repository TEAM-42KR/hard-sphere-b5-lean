import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_test_integrable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence_measurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_A
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_sphere_B
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
open scoped Classical
set_option maxHeartbeats 1000000
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceIncidence_test_integrable
    (G : Pt → Pt → Pt → ℝ)
    (hG : Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ D ∈ LamC, ∀ p ∈ FA, ∀ p' ∈ FB,
      dist D p = 1 → dist D p' = 1 → 0 < dist p p' → dist p p' < 1 → |G D p p'| ≤ C) :
    IntegrableOn (sourceTest G) sourceIncidence volume  := by
  change IntegrableOn (fun x => G (sourceCenter x) (sourceEndpointA x) (sourceEndpointB x) /
    (‖sourceCenter x‖ * ‖sourceCenter x-e‖)) sourceIncidence volume
  apply HardSphereB5.SphericalCrofton.Aux.Coarea.source_test_integrable G hG C hC hbound
    sourceIncidence HardSphereB5.SphericalCrofton.Aux.Coarea.sourceIncidence_measurable
  intro x hx
  rcases hx with ⟨hoff,hL,hR,hα,hβ,hp,hq,hz0,hz1⟩
  have hαπ : halfA (sourceCenter x) ≤ Real.pi := Real.arccos_le_pi _
  have hβπ : halfB (sourceCenter x) ≤ Real.pi := Real.arccos_le_pi _
  have ha : ‖sourceCenter x‖ ≤ 1 := by
    simpa [LamC,Metric.mem_closedBall,dist_zero_right] using hL.1
  have hb : ‖sourceCenter x-e‖ ≤ 1 := by
    simpa [LamC,Metric.mem_closedBall,dist_eq_norm] using hL.2
  have hu := HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_A (sourceCenter x) hoff (by linarith) (x 3)
  have hv := HardSphereB5.SphericalCrofton.Aux.Coarea.source_sphere_B (sourceCenter x) hoff (by linarith) (x 4)
  have hdp : dist (sourceCenter x) (sourceEndpointA x)=1 := by
    have hh : sourceCenter x-sourceEndpointA x = -u (sourceCenter x) (x 3) := by
      unfold sourceEndpointA; abel
    rw [dist_eq_norm,hh,norm_neg]
    exact hu.1
  have hdq : dist (sourceCenter x) (sourceEndpointB x)=1 := by
    have hh : sourceCenter x-sourceEndpointB x = -v (sourceCenter x) (x 4) := by
      unfold sourceEndpointB; abel
    rw [dist_eq_norm,hh,norm_neg]
    exact hv.1
  exact ⟨hL,⟨le_trans (neg_le_neg hαπ) hα.1,le_trans hα.2 hαπ⟩,
    ⟨le_trans (neg_le_neg hβπ) hβ.1,le_trans hβ.2 hβπ⟩,hp,hq,hdp,hdq,hz0,hz1⟩

