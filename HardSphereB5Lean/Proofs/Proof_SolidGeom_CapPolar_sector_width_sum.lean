import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_Profile
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
private lemma SolidGeom.CapPolar.winner_measurable (P : Profile) : Measurable (SolidGeom.CapPolar.winner P) := by
  unfold SolidGeom.CapPolar.winner
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · exact (measurableSet_le (P.rho_continuous 0).measurable (P.rho_continuous 1).measurable).inter
      (measurableSet_le (P.rho_continuous 0).measurable (P.rho_continuous 2).measurable)
  · exact measurableSet_le (P.rho_continuous 1).measurable (P.rho_continuous 2).measurable

private lemma SolidGeom.CapPolar.sum_sectors {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (P : Profile) (q : Fin 3 → ℝ → F)
    (hq : ∀ j, Continuous (q j)) :
    (∫ φ in Set.Icc 0 (2*Real.pi), q (SolidGeom.CapPolar.winner P φ) φ) =
      ∑ j : Fin 3, ∫ φ in SolidGeom.CapPolar.sector P j, q j φ := by
  let A : Fin 3 → Set ℝ := fun j => {φ | SolidGeom.CapPolar.winner P φ = j}
  have hA : ∀ j, MeasurableSet (A j) := fun j =>
    (SolidGeom.CapPolar.winner_measurable P) (MeasurableSet.singleton j)
  have hpoint : ∀ φ, q (SolidGeom.CapPolar.winner P φ) φ =
      ∑ j : Fin 3, (A j).indicator (q j) φ := by
    intro φ
    have hs : ∑ j : Fin 3, (A j).indicator (q j) φ = q (SolidGeom.CapPolar.winner P φ) φ := by
      calc
        _ = (A (SolidGeom.CapPolar.winner P φ)).indicator (q (SolidGeom.CapPolar.winner P φ)) φ := by
          apply Finset.sum_eq_single (SolidGeom.CapPolar.winner P φ)
          · intro j hj hne
            have hn : φ ∉ A j := by exact fun h => hne h.symm
            simp [hn]
          · simp
        _ = _ := by simp [A]
    exact hs.symm
  simp_rw [hpoint]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_indicator (hA j),Measure.restrict_restrict (hA j)]
    congr 1
    simp only [SolidGeom.CapPolar.sector,A,Set.inter_comm]
  · intro j hj
    exact ((hq j).integrableOn_Icc).indicator (hA j)

theorem proof_SolidGeom_CapPolar_sector_width_sum (P : Profile) :
    (∑ j : Fin 3, ∫ φ in sector P j, (1:ℝ))=2*Real.pi := by
  have hs := sum_sectors P (fun _ : Fin 3 => fun _ : ℝ => (1:ℝ))
    (fun _ => continuous_const)
  rw [← hs]
  simp [MeasureTheory.integral_const,Real.volume_Icc,ENNReal.toReal_ofReal,
    (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos).le]

#print axioms proof_SolidGeom_CapPolar_sector_width_sum
