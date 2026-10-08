import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_measurable_frame
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_contact_small_circle_subset
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_pair_arcs_subsets_circles_pullback
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
set_option maxHeartbeats 800000
theorem proof_HardSphereB5_SphericalCrofton_Aux_cross_arc_parameter_integral_aestronglyMeasurable (K : Pt × (Pt × Pt) → ℝ) (hK : Measurable K) : AEStronglyMeasurable (fun D : Pt => ∫ u in arcA D, ∫ v in arcB D, K (D,(u,v)) ∂arcMeasure ∂arcMeasure) (volume.restrict LamC)  := by
  obtain ⟨F1,F2,hF1,hF2,hF⟩ := SphereGeom.exists_measurable_frame
  let rA : Pt → ℝ := fun D => Real.sqrt (1 - ‖D‖ ^ 2 / 4)
  let rB : Pt → ℝ := fun D => Real.sqrt (1 - ‖D - e‖ ^ 2 / 4)
  let pA : Pt × ℝ → Pt := fun z => circlePt ((-(1/2 : ℝ)) • z.1)
    (F1 (nAv z.1)) (F2 (nAv z.1)) (rA z.1) z.2
  let pB : Pt × ℝ → Pt := fun z => circlePt ((-(1/2 : ℝ)) • (z.1-e))
    (F1 (nBv z.1)) (F2 (nBv z.1)) (rB z.1) z.2
  have hnAm : Measurable nAv := by unfold nAv; fun_prop
  have hnBm : Measurable nBv := by unfold nBv; fun_prop
  have hrAm : Measurable rA := by dsimp [rA]; fun_prop
  have hrBm : Measurable rB := by dsimp [rB]; fun_prop
  have hpA : Measurable pA := by dsimp [pA]; unfold circlePt; fun_prop
  have hpB : Measurable pB := by dsimp [pB]; unfold circlePt; fun_prop
  have hAset : MeasurableSet {z : Pt × Pt | z.2 ∈ arcA z.1} := by
    have heq : {z : Pt × Pt | z.2 ∈ arcA z.1} =
        {z : Pt × Pt | z.1 ≠ 0 ∧ ‖z.2‖ = 1 ∧ ‖z.1 + z.2‖ ≤ 1 ∧
          dist (z.1 + z.2) e ≤ 1 ∧ ‖z.1 + z.2‖ = 1} := by
      ext z
      by_cases h : z.1 = 0 <;> simp [arcA, SigmaD, LamC, h, and_assoc]
    rw [heq]
    measurability
  have hBset : MeasurableSet {z : Pt × Pt | z.2 ∈ arcB z.1} := by
    have heq : {z : Pt × Pt | z.2 ∈ arcB z.1} =
        {z : Pt × Pt | z.1 ≠ e ∧ ‖z.2‖ = 1 ∧ ‖z.1 + z.2‖ ≤ 1 ∧
          dist (z.1 + z.2) e ≤ 1 ∧ dist (z.1 + z.2) e = 1} := by
      ext z
      by_cases h : z.1 = e <;> simp [arcB, SigmaD, LamC, h, and_assoc]
    rw [heq]
    measurability

  let H : (Pt × ℝ) × ℝ → ℝ := fun z =>
    if pA z.1 ∈ arcA z.1.1 ∧ pB (z.1.1,z.2) ∈ arcB z.1.1
    then K (z.1.1,(pA z.1,pB (z.1.1,z.2))) else 0
  have hmap : Measurable (fun z : (Pt × ℝ) × ℝ =>
      (z.1.1,(pA z.1,pB (z.1.1,z.2)))) :=
    measurable_fst.fst.prodMk ((hpA.comp measurable_fst).prodMk
      (hpB.comp (measurable_fst.fst.prodMk measurable_snd)))
  have hH : Measurable H := (hK.comp hmap).ite
    ((hAset.preimage (measurable_fst.fst.prodMk (hpA.comp measurable_fst))).inter
      (hBset.preimage (measurable_fst.fst.prodMk
        (hpB.comp (measurable_fst.fst.prodMk measurable_snd))))) measurable_const
  let G : Pt → ℝ := fun D => rA D * rB D *
    ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π), H ((D,t),s)
  have hi : StronglyMeasurable (fun z : Pt × ℝ =>
    ∫ s in Set.Icc (0 : ℝ) (2 * π), H (z,s)) := hH.stronglyMeasurable.integral_prod_right'
  have ho : StronglyMeasurable (fun D : Pt =>
    ∫ t in Set.Icc (0 : ℝ) (2 * π), ∫ s in Set.Icc (0 : ℝ) (2 * π), H ((D,t),s)) := hi.integral_prod_right'
  have hG : StronglyMeasurable G := (hrAm.stronglyMeasurable.mul hrBm.stronglyMeasurable).mul ho
  apply hG.aestronglyMeasurable.congr
  have hLam : MeasurableSet LamC := measurableSet_closedBall.inter measurableSet_closedBall
  filter_upwards [ae_restrict_mem hLam] with D hD
  by_cases h0 : D = 0
  · simp [G,H,arcA,h0]
  by_cases he : D = e
  · simp [G,H,arcB,he]
  have h0B : D-e ≠ 0 := sub_ne_zero.mpr he
  have hnormA : ‖D‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hD.1
  have hnormB : ‖D-e‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hD.2
  have hrA : 0 < rA D := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg D])
  have hrB : 0 < rB D := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg (D-e)])
  have hnA : ‖nAv D‖ = 1 := by
    simp [nAv,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg D),
      norm_ne_zero_iff.mpr h0,inv_mul_cancel₀]
  have hnB : ‖nBv D‖ = 1 := by
    simp [nBv,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg (D-e)),
      norm_sub_rev e D,norm_ne_zero_iff.mpr h0B,inv_mul_cancel₀]
  let EA : Fin 3 → Pt := ![F1 (nAv D),F2 (nAv D),nAv D]
  let EB : Fin 3 → Pt := ![F1 (nBv D),F2 (nBv D),nBv D]
  have hEA : Orthonormal ℝ EA := hF _ hnA
  have hEB : Orthonormal ℝ EB := hF _ hnB
  have hpair (E : Fin 3 → Pt) (hE : Orthonormal ℝ E) : Orthonormal ℝ ![E 0,E 1] := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using orthonormal_iff_ite.mp hE (0 : Fin 3) (0 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (0 : Fin 3) (1 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (1 : Fin 3) (0 : Fin 3)
    · simpa using orthonormal_iff_ite.mp hE (1 : Fin 3) (1 : Fin 3)
  have hsubA : arcA D ⊆ circlePt ((-(1/2 : ℝ)) • D) (EA 0) (EA 1) (rA D) '' Set.Icc (0 : ℝ) (2*π) := by
    intro u hu
    apply SphereGeom.Aux.contact_small_circle_subset D hnormA h0 EA hEA (by simp [EA,nAv])
    simp only [arcA,if_neg h0,Set.mem_setOf_eq,SigmaD] at hu
    exact ⟨hu.1.1,hu.2⟩
  have hsubB : arcB D ⊆ circlePt ((-(1/2 : ℝ)) • (D-e)) (EB 0) (EB 1) (rB D) '' Set.Icc (0 : ℝ) (2*π) := by
    intro u hu
    apply SphereGeom.Aux.contact_small_circle_subset (D-e) hnormB h0B EB hEB
      (by change nBv D = ‖D-e‖⁻¹ • (-(D-e)); unfold nBv; congr 1; abel)
    simp only [arcB,if_neg he,Set.mem_setOf_eq,SigmaD] at hu
    refine ⟨hu.1.1,?_⟩
    rw [show (D-e)+u = D+u-e by abel]
    exact hu.2
  have hA : MeasurableSet (arcA D) := hAset.preimage (measurable_const.prodMk measurable_id)
  have hB : MeasurableSet (arcB D) := hBset.preimage (measurable_const.prodMk measurable_id)
  have hh := SphereGeom.Aux.pair_arcs_subsets_circles_pullback
    ((-(1/2 : ℝ)) • D) ((-(1/2 : ℝ)) • (D-e)) ![EA 0,EA 1] ![EB 0,EB 1]
    (hpair EA hEA) (hpair EB hEB) (rA D) (rB D) hrA hrB (arcA D) (arcB D)
    hA hB hsubA hsubB (fun uv => K (D,uv)) (hK.comp (measurable_const.prodMk measurable_id))
  convert hh.symm using 1 <;> rfl
