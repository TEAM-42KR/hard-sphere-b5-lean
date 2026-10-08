import Mathlib
set_option autoImplicit false

open MeasureTheory

theorem proof_SphereGeom_Aux_Crofton_monotone_eq_measure_on_measurable_of_sigmaCompact (F : Set ℝ → ENNReal) (hF : Monotone F)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ)
    (hEq : ∀ T : Set ℝ, T ⊆ Set.Icc a b → IsSigmaCompact T → F T = ν T)
    (S : Set ℝ) (hS : MeasurableSet S) (hSab : S ⊆ Set.Icc a b) :
    F S = ν S := by
  apply le_antisymm
  · rw [S.measure_eq_iInf_isOpen ν]
    refine le_iInf fun U => le_iInf fun hSU => le_iInf fun hU => ?_
    have hloc : IsLocallyClosed (U ∩ Set.Icc a b) :=
      hU.isLocallyClosed.inter isClosed_Icc.isLocallyClosed
    letI : LocallyCompactSpace ↥(U ∩ Set.Icc a b) := hloc.locallyCompactSpace
    have hσ : IsSigmaCompact (U ∩ Set.Icc a b) :=
      isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
    calc
      F S ≤ F (U ∩ Set.Icc a b) := hF (Set.subset_inter hSU hSab)
      _ = ν (U ∩ Set.Icc a b) := hEq _ Set.inter_subset_right hσ
      _ ≤ ν U := measure_mono Set.inter_subset_left
  · rw [hS.measure_eq_iSup_isCompact ν]
    refine iSup_le fun K => iSup_le fun hKS => iSup_le fun hK => ?_
    rw [← hEq K (hKS.trans hSab) hK.isSigmaCompact]
    exact hF hKS
