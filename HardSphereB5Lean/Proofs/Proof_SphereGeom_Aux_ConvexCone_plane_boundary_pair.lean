import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_ConvexCone_positive_smul_transport
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_ConvexCone_line_frontier_unique
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_ConvexCone_plane_transverse_coordinates
set_option autoImplicit false
open SphereGeom Filter
open scoped Topology

theorem proof_SphereGeom_Aux_ConvexCone_plane_boundary_pair (C : Set E3) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hzero : (0 : E3) ∈ C)
    (hscale : ∀ (r : ℝ), 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (p : E3) (hp : ‖p‖ = 1)
    (hinter : ∃ v ∈ interior C, inner ℝ p v = 0)
    (hhalf : ∃ n : E3, n ≠ 0 ∧ ∀ v ∈ C, 0 ≤ inner ℝ n v) :
    ∃ a b : E3, a ≠ b ∧ greatCircle p ∩ frontier C = {a,b} := by
  classical
  obtain ⟨v, hv, hpv⟩ := hinter
  obtain ⟨n, hn, hh⟩ := hhalf
  have hnv : 0 < inner ℝ n v := by
    have hnonneg := hh v (interior_subset hv)
    by_contra hpos
    have hnv0 : inner ℝ n v = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
    have hnn : 0 < inner ℝ n n := real_inner_self_pos.mpr hn
    have hcont : ContinuousAt (fun d : ℝ => v - d • n) 0 := by fun_prop
    have hnear : ∀ᶠ d in 𝓝 (0 : ℝ), v - d • n ∈ interior C := by
      apply hcont.eventually
      simpa using isOpen_interior.mem_nhds hv
    have hnear' := hnear.filter_mono
      (show 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have hm : ∀ᶠ d in 𝓝[Set.Ioi (0 : ℝ)] 0, d ∈ Set.Ioi (0 : ℝ) :=
      self_mem_nhdsWithin
    obtain ⟨d, hdv, hd⟩ := (hnear'.and hm).exists
    have hdpos : 0 < d := hd
    have hbad := hh (v - d • n) (interior_subset hdv)
    simp only [inner_sub_right, inner_smul_right, hnv0] at hbad
    nlinarith
  have hvne : v ≠ 0 := by
    intro hz
    simp [hz] at hnv
  obtain ⟨w, hpw, hli, hspan⟩ :=
    SphereGeom.Aux.ConvexCone.plane_transverse_coordinates p v hp hvne hpv
  obtain ⟨s, hs, hsu⟩ :=
    SphereGeom.Aux.ConvexCone.line_frontier_unique C hclosed hconvex hscale v n w hv hnv hh
  obtain ⟨t, ht, htu⟩ :=
    SphereGeom.Aux.ConvexCone.line_frontier_unique C hclosed hconvex hscale v n (-w) hv hnv hh
  let A : E3 := w + s • v
  let B : E3 := -w + t • v
  have hA : A ≠ 0 := by
    intro hz
    have he : s • v + (1 : ℝ) • w = 0 := by simpa [A, add_comm] using hz
    have hh := (hli.eq_zero_of_pair he).2
    norm_num at hh
  have hB : B ≠ 0 := by
    intro hz
    have he : t • v + (-1 : ℝ) • w = 0 := by simpa [B, add_comm] using hz
    have hh := (hli.eq_zero_of_pair he).2
    norm_num at hh
  have hNA : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hNB : 0 < ‖B‖ := norm_pos_iff.mpr hB
  let a : E3 := ‖A‖⁻¹ • A
  let b : E3 := ‖B‖⁻¹ • B
  have haunit : ‖a‖ = 1 := by
    simp [a, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNA), ne_of_gt hNA]
  have hbunit : ‖b‖ = 1 := by
    simp [b, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNB), ne_of_gt hNB]
  have hap : inner ℝ p a = 0 := by
    simp [a, A, inner_smul_right, inner_add_right, hpw, hpv]
  have hbp : inner ℝ p b = 0 := by
    simp [b, B, inner_smul_right, inner_add_right, hpw, hpv]
  have hafront : a ∈ frontier C :=
    (SphereGeom.Aux.ConvexCone.positive_smul_transport C hscale
      ‖A‖⁻¹ (inv_pos.mpr hNA) A).2.mpr hs
  have hbfront : b ∈ frontier C :=
    (SphereGeom.Aux.ConvexCone.positive_smul_transport C hscale
      ‖B‖⁻¹ (inv_pos.mpr hNB) B).2.mpr ht
  have hab : a ≠ b := by
    intro heq
    have he : (‖A‖⁻¹ * s) • v + ‖A‖⁻¹ • w =
        (‖B‖⁻¹ * t) • v + (-‖B‖⁻¹) • w := by
      convert heq using 1 <;> dsimp [a, b, A, B] <;> module
    have hcoeff := (hli.eq_of_pair he).2
    have hpa : 0 < ‖A‖⁻¹ := inv_pos.mpr hNA
    have hpb : 0 < ‖B‖⁻¹ := inv_pos.mpr hNB
    linarith
  refine ⟨a, b, hab, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hxnorm : ‖x‖ = 1 := hx.1.1
    have hxperp : inner ℝ p x = 0 := hx.1.2
    have hxfront : x ∈ frontier C := hx.2
    have hxc : x ∈ C := by simpa only [hclosed.closure_eq] using hxfront.1
    obtain ⟨u, z, hxrep⟩ := hspan x hxperp
    have hz : z ≠ 0 := by
      intro hz0
      have hum : u ≠ 0 := by
        intro hu0
        have hx0 : x = 0 := by simpa [hz0, hu0] using hxrep
        simp [hx0] at hxnorm
      have hnn := hh x hxc
      rw [hxrep] at hnn
      simp only [hz0, zero_smul, add_zero, inner_smul_right] at hnn
      have humul : 0 ≤ u * inner ℝ n v := hnn
      have hupos : 0 < u := by
        have hu0 : 0 ≤ u := nonneg_of_mul_nonneg_left humul hnv
        exact lt_of_le_of_ne hu0 (Ne.symm hum)
      have hint : u • v ∈ interior C :=
        (SphereGeom.Aux.ConvexCone.positive_smul_transport C hscale u hupos v).1.mpr hv
      apply hxfront.2
      simpa [hxrep, hz0] using hint
    rcases lt_or_gt_of_ne hz with hzneg | hzpos
    · have hd : 0 < -z := neg_pos.mpr hzneg
      have hfactor : (-z)⁻¹ • x = -w + (u / (-z)) • v := by
        rw [hxrep]
        simp [smul_add, smul_smul, div_eq_mul_inv, hz] <;> module
      have hxf : -w + (u / (-z)) • v ∈ frontier C := by
        rw [← hfactor]
        exact (SphereGeom.Aux.ConvexCone.positive_smul_transport C hscale
          (-z)⁻¹ (inv_pos.mpr hd) x).2.mpr hxfront
      have hcoef := htu _ hxf
      have hxB : x = (-z) • B := by
        calc
          x = (-z) • ((-z)⁻¹ • x) := by simp [smul_smul, hz]
          _ = (-z) • (-w + (u / (-z)) • v) := by rw [hfactor]
          _ = (-z) • B := by rw [hcoef] <;> rfl
      have hnorm : (-z) * ‖B‖ = 1 := by
        simpa only [hxB, norm_smul, Real.norm_eq_abs, abs_of_pos hd] using hxnorm
      have hzval : -z = ‖B‖⁻¹ :=
        mul_right_cancel₀ (ne_of_gt hNB) (hnorm.trans (inv_mul_cancel₀ (ne_of_gt hNB)).symm)
      have heqb : x = b := by rw [hxB, hzval] <;> rfl
      simp [heqb]
    · have hfactor : z⁻¹ • x = w + (u / z) • v := by
        rw [hxrep]
        simp [smul_add, smul_smul, div_eq_mul_inv, hz] <;> module
      have hxf : w + (u / z) • v ∈ frontier C := by
        rw [← hfactor]
        exact (SphereGeom.Aux.ConvexCone.positive_smul_transport C hscale
          z⁻¹ (inv_pos.mpr hzpos) x).2.mpr hxfront
      have hcoef := hsu _ hxf
      have hxA : x = z • A := by
        calc
          x = z • (z⁻¹ • x) := by simp [smul_smul, ne_of_gt hzpos]
          _ = z • (w + (u / z) • v) := by rw [hfactor]
          _ = z • A := by rw [hcoef] <;> rfl
      have hnorm : z * ‖A‖ = 1 := by
        simpa only [hxA, norm_smul, Real.norm_eq_abs, abs_of_pos hzpos] using hxnorm
      have hzval : z = ‖A‖⁻¹ :=
        mul_right_cancel₀ (ne_of_gt hNA) (hnorm.trans (inv_mul_cancel₀ (ne_of_gt hNA)).symm)
      have heqa : x = a := by rw [hxA, hzval] <;> rfl
      simp [heqa]
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨⟨haunit, hap⟩, hafront⟩
    · have hxb : x = b := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨⟨hbunit, hbp⟩, hbfront⟩
