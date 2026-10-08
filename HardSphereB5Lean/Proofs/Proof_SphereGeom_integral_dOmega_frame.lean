import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_dOmega_map_linearIsometryEquiv
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_SphericalCoordinates_standardIntegral
set_option autoImplicit false

open MeasureTheory SphereGeom

noncomputable section

theorem proof_SphereGeom_integral_dOmega_frame {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : Fin 3 → E3) (he : Orthonormal ℝ e) (f : E3 → F) (hf : Integrable f dOmega) :
    ∫ u, f u ∂dOmega =
      ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Real.sin θ • f ((Real.sin θ * Real.cos φ) • e 0 + (Real.sin θ * Real.sin φ) • e 1 +
          Real.cos θ • e 2) := by
  let b : OrthonormalBasis (Fin 3) ℝ E3 :=
    OrthonormalBasis.mk he
      (he.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [E3])).ge
  let R : E3 ≃ₗᵢ[ℝ] E3 :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).equiv b (Equiv.refl _)
  have hRbasis (i : Fin 3) : R ((EuclideanSpace.basisFun (Fin 3) ℝ) i) = e i := by
    change (EuclideanSpace.basisFun (Fin 3) ℝ).equiv b (Equiv.refl _) _ = e i
    rw [OrthonormalBasis.equiv_apply_basis]
    simp only [Equiv.refl_apply, b, OrthonormalBasis.coe_mk]
  have hR : MeasurePreserving R dOmega dOmega :=
    ⟨R.continuous.measurable, SphereGeom.dOmega_map_linearIsometryEquiv R⟩
  have hRe : MeasurableEmbedding R := R.toHomeomorph.measurableEmbedding
  have hfR : Integrable (f ∘ R) dOmega := (hR.integrable_comp_emb hRe).mpr hf
  calc
    ∫ u, f u ∂dOmega = ∫ u, (f ∘ R) u ∂dOmega := (hR.integral_comp hRe f).symm
    _ = ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          Real.sin θ • (f ∘ R)
            ((Real.sin θ * Real.cos φ) • (EuclideanSpace.basisFun (Fin 3) ℝ) 0 +
              (Real.sin θ * Real.sin φ) • (EuclideanSpace.basisFun (Fin 3) ℝ) 1 +
              Real.cos θ • (EuclideanSpace.basisFun (Fin 3) ℝ) 2) :=
      SphereGeom.Aux.SphericalCoordinates.standardIntegral (f ∘ R) hfR
    _ = _ := by simp only [Function.comp_apply, map_add, map_smul, hRbasis]
