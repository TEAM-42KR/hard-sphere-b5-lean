import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_CircleEndpointAtlas
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_unit_plane_cross_orientation
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_pole_orientation
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_radial_regular
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Cap_sigma_caps_data
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_sigma_axis_cases
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_frontierSigma_subset_arcs
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Endpoint
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_circle_atlas_oriented_fiber (D : Pt) (hD : D ∈ LamC) (hK : IsRegularRegionCrofton (SigmaD D))
    (C : CircleEndpointAtlas) (hC : IsCircleEndpointAtlas D C) (F : Set Pt)
    (hcover : atlasGamma C '' atlasInterval C = sFrontier (SigmaD D) \ F)
    (p : Pt) (hp : ‖p‖ = 1) (havoid : greatCircle p ∩ F = ∅)
    (hcard : ((greatCircle p ∩ sFrontier (SigmaD D)).encard : ENNReal) =
      if p ∈ hitPoleSet D then 2 else 0)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    ({x : Pt | x ∈ atlasRadialSource C ∧ atlasRadial C x = r • p}.encard : ENNReal) =
      if p ∈ hitPoleSet D then 1 else 0 := by
  classical
  let γ : ℝ → Pt := atlasGamma C
  let B : Set Pt := greatCircle p ∩ sFrontier (SigmaD D)
  have hpnz : p ≠ -p := by
    intro hh
    have hzero : p = 0 := by
      ext i
      have hi : p i = -p i := congrArg (fun z : Pt => z i) hh
      change p i = 0
      linarith
    simpa [hzero] using hp
  have hfront (u : Pt) (hu : u ∈ sFrontier (SigmaD D)) : u ∈ SigmaD D := by
    have hmem := Aux.frontierSigma_subset_arcs D hu
    rcases hmem with hmem | hmem
    · by_cases h0 : D = 0
      · simp [arcA, h0] at hmem
      · simp only [arcA, if_neg h0, Set.mem_setOf_eq] at hmem
        exact hmem.1
    · by_cases he : D = e
      · simp [arcB, he] at hmem
      · simp only [arcB, if_neg he, Set.mem_setOf_eq] at hmem
        exact hmem.1
  have hanti (u v : Pt) (hu : u ∈ SigmaD D) (hv : v ∈ SigmaD D) : u ≠ -v := by
    by_cases h0 : D = 0
    · rw [h0, sigma_axis_cases.2.1.1] at hu hv
      intro hh
      have h1 := hu.2
      rw [hh, inner_neg_right] at h1
      linarith [hv.2]
    by_cases he : D = e
    · rw [he, sigma_axis_cases.2.2.1] at hu hv
      intro hh
      have h1 := hu.2
      rw [hh, inner_neg_right] at h1
      linarith [hv.2]
    have hc := (Aux.Cap.sigma_caps_data D h0 he).2.2
    rw [hc] at hu hv
    intro hh
    have h1 := hu.1.2
    have h2 := hv.1.2
    rw [hh, inner_neg_right] at h1
    have hn : 0 < ‖D‖ := norm_pos_iff.mpr h0
    linarith
  have hnorm (x : Pt) (hx : x ∈ atlasRadialSource C) : ‖atlasRadial C x‖ = x 2 := by
    have hn : ‖pairPole (atlasPair C x)‖ = 1 :=
      (pole_orientation (γ (x 0)) (γ (x 1))).2.2.2 hx.2.2.2
    change ‖(x 2) • pairPole (atlasPair C x)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hx.2.2.1.1, hn, mul_one]
  have hrpn : ‖r • p‖ = r := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hp, mul_one]
  have hrdir : ‖r • p‖⁻¹ • (r • p) = p := by
    rw [hrpn, smul_smul, inv_mul_cancel₀ (ne_of_gt hr.1), one_smul]
  have hpair (x : Pt) (hx : x ∈ atlasRadialSource C) (hy : atlasRadial C x = r • p) :
      x 2 = r ∧ γ (x 0) ∈ B ∧ γ (x 1) ∈ B ∧ γ (x 0) ≠ γ (x 1) ∧
      pairPole (atlasPair C x) = p := by
    have hxy : x 2 = r := by rw [← hnorm x hx, hy, hrpn]
    have hd := (circle_atlas_radial_regular D C hC).2.2.2.2.2 x hx
    rw [hy, hrdir] at hd
    have hq : pairPole (atlasPair C x) = p := hd.symm
    have hpf := pole_orientation (γ (x 0)) (γ (x 1))
    have hq0 : unitDir (cross (γ (x 0)) (γ (x 1))) = p := hq
    have hgc1 : γ (x 0) ∈ greatCircle p := ⟨hC.unit _ hx.1, by rw [← hq0]; exact hpf.2.1⟩
    have hgc2 : γ (x 1) ∈ greatCircle p := ⟨hC.unit _ hx.2.1, by rw [← hq0]; exact hpf.2.2.1⟩
    have hf1 : γ (x 0) ∈ sFrontier (SigmaD D) := by
      have hh : γ (x 0) ∈ atlasGamma C '' atlasInterval C := ⟨x 0, hx.1, rfl⟩
      rw [hcover] at hh
      exact hh.1
    have hf2 : γ (x 1) ∈ sFrontier (SigmaD D) := by
      have hh : γ (x 1) ∈ atlasGamma C '' atlasInterval C := ⟨x 1, hx.2.1, rfl⟩
      rw [hcover] at hh
      exact hh.1
    have hne : γ (x 0) ≠ γ (x 1) := by
      intro hh
      apply hx.2.2.2
      change cross (γ (x 0)) (γ (x 1)) = 0
      rw [hh]
      ext i
      fin_cases i <;> simp [cross, cross_apply] <;> ring
    exact ⟨hxy, ⟨hgc1, hf1⟩, ⟨hgc2, hf2⟩, hne, hq⟩
  by_cases hhit : p ∈ hitPoleSet D
  · rw [if_pos hhit] at hcard ⊢
    have hc : B.encard = 2 := by exact_mod_cast hcard
    obtain ⟨u, v, huv, hB⟩ := Set.encard_eq_two.mp hc
    have hu : u ∈ B := by rw [hB]; simp
    have hv : v ∈ B := by rw [hB]; simp
    have hana := hanti u v (hfront u hu.2) (hfront v hv.2)
    have ho := unit_plane_cross_orientation u v p hu.1.1 hv.1.1 hp huv hana hu.1.2 hv.1.2
    have hex : ∃ a b, a ≠ b ∧ B = {a,b} ∧ unitDir (cross a b) = p ∧
        unitDir (cross b a) = -p ∧ cross a b ≠ 0 := by
      rcases ho.2 with ho | ho
      · exact ⟨u,v,huv,hB,ho.1,ho.2,(unit_plane_cross_orientation u v p
          hu.1.1 hv.1.1 hp huv hana hu.1.2 hv.1.2).1⟩
      · refine ⟨v,u,huv.symm,?_,ho.2,ho.1,?_⟩
        · simpa only [Set.pair_comm] using hB
        · intro hz
          have hn : unitDir (cross v u) = 0 := by simp [hz,unitDir]
          rw [ho.2] at hn
          simpa [hn] using hp
    obtain ⟨a,b,hab,hB,hpole,hswap,hcross⟩ := hex
    have ha : a ∈ B := by rw [hB]; simp
    have hb : b ∈ B := by rw [hB]; simp
    have hparam (z : Pt) (hz : z ∈ B) : ∃ t ∈ atlasInterval C, γ t = z := by
      have hF : z ∉ F := by
        intro hzF
        have hh : z ∈ greatCircle p ∩ F := ⟨hz.1,hzF⟩
        rw [havoid] at hh
        exact hh
      have hi : z ∈ atlasGamma C '' atlasInterval C := by rw [hcover]; exact ⟨hz.2,hF⟩
      exact hi
    obtain ⟨t, ht, hta⟩ := hparam a ha
    obtain ⟨s, hs, hsb⟩ := hparam b hb
    let x0 : Pt := WithLp.toLp 2 ![t,s,r]
    have hx0 : x0 ∈ atlasRadialSource C := by
      change t ∈ atlasInterval C ∧ s ∈ atlasInterval C ∧ r ∈ Set.Ioo (0 : ℝ) 1 ∧ cross (γ t) (γ s) ≠ 0
      exact ⟨ht,hs,hr,by rwa [hta,hsb]⟩
    have hy0 : atlasRadial C x0 = r • p := by
      change r • unitDir (cross (γ t) (γ s)) = _
      rw [hta,hsb,hpole]
    have hsing : {x : Pt | x ∈ atlasRadialSource C ∧ atlasRadial C x = r • p} = {x0} := by
      ext x
      constructor
      · rintro ⟨hx,hy⟩
        obtain ⟨hxr,h1,h2,hneq,hq⟩ := hpair x hx hy
        rw [hB] at h1 h2
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
        have hpairs : γ (x 0) = a ∧ γ (x 1) = b := by
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · exact False.elim (hneq (h1.trans h2.symm))
          · exact ⟨h1,h2⟩
          · have hh : pairPole (atlasPair C x) = -p := by
              change unitDir (cross (γ (x 0)) (γ (x 1))) = _
              rw [h1,h2,hswap]
            exact False.elim (hpnz (hq.symm.trans hh))
          · exact False.elim (hneq (h1.trans h2.symm))
        have hx0' : x 0 = t := hC.injective hx.1 ht (hpairs.1.trans hta.symm)
        have hx1' : x 1 = s := hC.injective hx.2.1 hs (hpairs.2.trans hsb.symm)
        apply Set.mem_singleton_iff.mpr
        ext i
        fin_cases i <;> simp [x0,hx0',hx1',hxr]
      · intro hx
        have hx' : x = x0 := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨hx0,hy0⟩
    rw [hsing]
    simp
  · rw [if_neg hhit] at hcard ⊢
    have hempty : B = ∅ := by
      have hc : B.encard = 0 := by exact_mod_cast hcard
      exact Set.encard_eq_zero.mp hc
    have hfiber : {x : Pt | x ∈ atlasRadialSource C ∧ atlasRadial C x = r • p} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh := (hpair x hx.1 hx.2).2.1
      rw [hempty] at hh
      exact hh
    rw [hfiber]
    simp
