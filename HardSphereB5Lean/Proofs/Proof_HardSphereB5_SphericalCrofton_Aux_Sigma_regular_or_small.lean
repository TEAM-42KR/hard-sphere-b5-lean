import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_sigma_caps_data
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_strict_midpoint
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_strict_point_interior
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_sigma_axis_cases
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_capInter_isRegularRegionCrofton
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem proof_HardSphereB5_SphericalCrofton_Aux_Sigma_regular_or_small (D : Pt) (hD : D ∈ LamC) :
    IsRegularRegionCrofton (SigmaD D) ∨ (SigmaD D).Subsingleton := by
  have hclass (N : ℕ) (hN : 0 < N) (n : Fin N → Pt) (h : Fin N → ℝ)
      (hn : ∀ i, ‖n i‖ = 1) (hpos : ∀ i, 0 < h i) :
      IsRegularRegionCrofton (⋂ i, cap (n i) (h i)) ∨ (⋂ i, cap (n i) (h i)).Subsingleton := by
    by_cases hs : (⋂ i, cap (n i) (h i)).Subsingleton
    · exact Or.inr hs
    · obtain ⟨u, hu, v, hv, huv⟩ := Set.not_subsingleton_iff.mp hs
      let i₀ : Fin N := ⟨0, hN⟩
      have hcu : ∀ i, h i ≤ inner ℝ (n i) u := fun i => (Set.mem_iInter.mp hu i).2
      have hcv : ∀ i, h i ≤ inner ℝ (n i) v := fun i => (Set.mem_iInter.mp hv i).2
      have hun : ‖u‖ = 1 := (Set.mem_iInter.mp hu i₀).1
      have hvn : ‖v‖ = 1 := (Set.mem_iInter.mp hv i₀).1
      have hnon : u ≠ -v := by
        intro heq
        have ha := hcu i₀
        have hb := hcv i₀
        rw [heq, inner_neg_right] at ha
        linarith [hpos i₀]
      obtain ⟨w, hw⟩ := Aux.Cap.strict_midpoint N n h hpos u v hun hvn hcu hcv huv hnon
      exact Or.inl (capInter_isRegularRegionCrofton N hN n h hn (fun i => (hpos i).le)
        (Aux.Cap.strict_point_interior N n h w hw))
  have hone (a : Pt) (ha : ‖a‖ = 1) :
      IsRegularRegionCrofton (cap a (1 / 2)) ∨ (cap a (1 / 2)).Subsingleton := by
    simpa only [Set.iInter_const] using
      hclass 1 (by norm_num) (fun _ => a) (fun _ => (1 / 2 : ℝ))
        (fun _ => ha) (fun _ => by norm_num)
  have he : ‖e‖ = 1 := by simp [HardSphereB5.Lean.e]
  by_cases hD0 : D = 0
  · subst D
    rw [sigma_axis_cases.2.1.1]
    exact hone e he
  by_cases hDe : D = e
  · subst D
    rw [sigma_axis_cases.2.2.1]
    exact hone (-e) (by simpa using he)
  obtain ⟨hnA, hnB, hrep⟩ := Aux.Cap.sigma_caps_data D hD0 hDe
  let n : Fin 2 → Pt := ![nAv D, nBv D]
  let h : Fin 2 → ℝ := ![‖D‖ / 2, ‖D - e‖ / 2]
  have hn : ∀ i, ‖n i‖ = 1 := by
    intro i
    fin_cases i <;> simp [n, hnA, hnB]
  have hpos : ∀ i, 0 < h i := by
    intro i
    have hA : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD0
    have hB : (0 : ℝ) < ‖D - e‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hDe)
    fin_cases i
    · change 0 < ‖D‖ / 2
      exact div_pos hA (by norm_num)
    · change 0 < ‖D - e‖ / 2
      exact div_pos hB (by norm_num)
  have hset : (⋂ i, cap (n i) (h i)) = SigmaD D := by
    rw [hrep]
    ext u
    simp [n, h, Set.mem_iInter, Fin.forall_fin_two]
  rw [← hset]
  exact hclass 2 (by norm_num) n h hn hpos

#print axioms proof_HardSphereB5_SphericalCrofton_Aux_Sigma_regular_or_small
