import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_source_coordinates_preserving
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
noncomputable section
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_coordinate_integral (f : Chart5 → ℝ) (hf : Integrable f) :
    (∫ x, f x) = ∫ D : Pt, ∫ α : ℝ, ∫ β : ℝ,
      f (pack5 (D 0) (D 1) (D 2) α β)  := by
  let E : Chart5 ≃ᵐ (Pt × ℝ × ℝ) :=
    { toEquiv :=
      { toFun := fun x => (sourceCenter x, x 3, x 4)
        invFun := fun q => pack5 (q.1 0) (q.1 1) (q.1 2) q.2.1 q.2.2
        left_inv := by
          intro x
          ext i
          fin_cases i <;> simp [sourceCenter, pack5, e, e1, e2]
        right_inv := by
          intro q
          apply Prod.ext
          · ext i
            fin_cases i <;> simp [sourceCenter, pack5, e, e1, e2]
          · apply Prod.ext <;> simp [pack5] }
      measurable_toFun := HardSphereB5.SphericalCrofton.Aux.Coarea.source_coordinates_preserving.measurable
      measurable_invFun := by
        change Measurable (fun q : Pt × ℝ × ℝ => pack5 (q.1 0) (q.1 1) (q.1 2) q.2.1 q.2.2)
        unfold pack5
        fun_prop }
  have hE : MeasurePreserving E := HardSphereB5.SphericalCrofton.Aux.Coarea.source_coordinates_preserving
  have hEs : MeasurePreserving E.symm := hE.symm
  have hint : Integrable (fun q : Pt × ℝ × ℝ => f (E.symm q)) :=
    (hEs.integrable_comp_emb E.symm.measurableEmbedding).mpr hf
  calc
    (∫ x, f x) = ∫ q : Pt × ℝ × ℝ, f (E.symm q) := (hEs.integral_comp' f).symm
    _ = ∫ D : Pt, ∫ t : ℝ × ℝ, f (E.symm (D,t)) := integral_prod _ hint
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hint.prod_right_ae] with D hD
      exact integral_prod _ hD

