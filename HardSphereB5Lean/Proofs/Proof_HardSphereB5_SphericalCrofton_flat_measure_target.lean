import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_coarea_transport
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_flat_measure_reflection_even
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_kernel_integrable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_representative_geometry
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_circInt_isometry_invariant
set_option autoImplicit false

open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 900000

theorem proof_HardSphereB5_SphericalCrofton_flat_measure_target (f : Kern) :
    frakB f = π * ∫ v in Dnear,
      (1 / √(Hpoly v.1 v.2.1 v.2.2)) * (rhoK f (1 - v.2.2 / 2) / √v.2.2) *
        circInt (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) := by
  let K : Pt → Pt → ℝ := fun p p' =>
    if 0 < dist p p' ∧ dist p p' < 1 then
      rhoK f (1-dist p p'^2/2) / dist p p' * circInt p p' else 0
  have hKi : Integrable (Function.uncurry K)
      (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)) :=
    Aux.Coarea.kernel_integrable f
  have hKinv : ∀ R : Pt ≃ₗᵢ[ℝ] Pt, R e=e → ∀ p ∈ FA, ∀ p' ∈ FB,
      K (R p) (R p')=K p p' := by
    intro R hR p hp p' hp'
    simp only [K, R.dist_map, circInt_isometry_invariant p p' R hR]
  let W : (ℝ × ℝ × ℝ) → ℝ := fun v =>
    (1 / √(Hpoly v.1 v.2.1 v.2.2)) * (rhoK f (1-v.2.2/2) / √v.2.2) *
      circInt (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2))
  let C : Set (ℝ × ℝ × ℝ) := {v | 0<v.2.2 ∧ v.2.2<1}
  have hC : MeasurableSet C :=
    (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)).inter
      (measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const)
  have hD : MeasurableSet Dfull := by
    dsimp [Dfull,Hpoly]
    measurability
  have hset : C ∩ Dfull=Dnear := by
    ext v
    simp only [C,Dnear,Set.mem_inter_iff,Set.mem_setOf_eq]
    tauto
  have hrep (v : ℝ × ℝ × ℝ) (hv : v ∈ Dfull) :
      K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) /
        √(Hpoly v.1 v.2.1 v.2.2) = C.indicator W v := by
    rcases Aux.Coarea.representative_geometry v hv with ⟨hp,hp',hs,hdist⟩
    have hsqrt := Real.sq_sqrt hs.le
    have hsn := Real.sqrt_nonneg v.2.2
    have hcut : (0 < dist (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) ∧
        dist (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) < 1) ↔
        (0<v.2.2 ∧ v.2.2<1) := by
      rw [hdist]
      constructor
      · intro hh
        exact ⟨hs, by nlinarith [hh.2]⟩
      · intro hh
        exact ⟨Real.sqrt_pos.2 hs, by nlinarith [hh.2]⟩
    dsimp only [K]
    by_cases hnear : v ∈ C
    · rw [if_pos (hcut.mpr hnear),Set.indicator_of_mem hnear,hdist,hsqrt]
      dsimp only [W]
      ring
    · rw [if_neg (fun hh => hnear (hcut.mp hh)),Set.indicator_of_notMem hnear,zero_div]
  have hI : ∫ v in Dfull,
      K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) /
        √(Hpoly v.1 v.2.1 v.2.2) = ∫ v in Dnear, W v := by
    calc
      _ = ∫ v in Dfull, C.indicator W v := setIntegral_congr_fun hD hrep
      _ = ∫ v in Dnear, W v := by
        rw [integral_indicator hC,Measure.restrict_restrict hC,hset]
  calc
    frakB f = ∫ p in FA, ∫ p' in FB, K p p'
        ∂sphereMeasure e ∂sphereMeasure 0 := coarea_transport f
    _ = π * ∫ v in Dfull,
        K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) /
          √(Hpoly v.1 v.2.1 v.2.2) := flat_measure_reflection_even K hKi hKinv
    _ = π * ∫ v in Dnear, W v := by rw [hI]
