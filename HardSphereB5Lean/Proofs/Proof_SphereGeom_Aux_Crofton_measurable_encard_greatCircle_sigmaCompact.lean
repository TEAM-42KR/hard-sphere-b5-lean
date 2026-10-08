import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_measurable_encard_greatCircle_compact
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_encard_monotone_iUnion
set_option autoImplicit false
open MeasureTheory SphereGeom
open scoped Classical
noncomputable section
theorem proof_SphereGeom_Aux_Crofton_measurable_encard_greatCircle_sigmaCompact (A : Set E3) (hA : IsSigmaCompact A) :
    Measurable (fun p : E3 => ((greatCircle p ∩ A).encard : ENNReal)) := by
  classical
  obtain ⟨K, hK, hcov⟩ := hA
  let B : ℕ → Set E3 := fun n => ⋃ j ∈ Finset.range (n + 1), K j
  have hB (n : ℕ) : IsCompact (B n) := (Finset.range (n + 1)).finite_toSet.isCompact_biUnion (fun j _ => hK j)
  have hmon : Monotone B := by
    intro n m hnm x hx
    change x ∈ ⋃ j ∈ Finset.range (n + 1), K j at hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hj', hxj⟩ := Set.mem_iUnion.mp hj
    change x ∈ ⋃ j ∈ Finset.range (m + 1), K j
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj') (Nat.add_le_add_right hnm 1)), hxj⟩⟩
  have hcovB : (⋃ n, B n) = A := by
    rw [← hcov]
    ext x
    constructor
    · intro hx
      obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨j, hx⟩
    · intro hx
      obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self j), hx⟩⟩⟩
  have hsup (p : E3) : ((greatCircle p ∩ A).encard : ENNReal) =
      ⨆ n, ((greatCircle p ∩ B n).encard : ENNReal) := by
    have he : (greatCircle p ∩ A).encard = ⨆ n, (greatCircle p ∩ B n).encard := by
      rw [← hcovB, Set.inter_iUnion]
      apply SphereGeom.Aux.Crofton.encard_monotone_iUnion
      intro n m hnm
      exact Set.inter_subset_inter_right _ (hmon hnm)
    change ENat.toENNReal ((greatCircle p ∩ A).encard) = ⨆ n, ENat.toENNReal ((greatCircle p ∩ B n).encard)
    rw [he, ENat.toENNReal_iSup]
  rw [show (fun p : E3 => ((greatCircle p ∩ A).encard : ENNReal)) =
      (fun p : E3 => ⨆ n, ((greatCircle p ∩ B n).encard : ENNReal)) from funext hsup]
  exact Measurable.iSup (fun n => SphereGeom.Aux.Crofton.measurable_encard_greatCircle_compact (B n) (hB n))
