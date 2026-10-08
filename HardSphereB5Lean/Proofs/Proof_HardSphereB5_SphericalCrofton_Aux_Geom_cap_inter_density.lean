import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_CapIntersection_basic_properties
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_inter_density (N : ℕ) (hN : 0 < N) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m)
    (hint : (sInterior (⋂ m, cap (n m) (h m))).Nonempty) :
    (⋂ m, cap (n m) (h m)) = closure (sInterior (⋂ m, cap (n m) (h m))) := by
  let K := ⋂ m, cap (n m) (h m)
  let C : Set Pt := {v | ∀ m, h m * ‖v‖ ≤ inner ℝ (n m) v}
  let P : Set Pt := {v | v ≠ 0}
  let f : Pt → Pt := fun v => ‖v‖⁻¹ • v
  have hP : IsOpen P := isClosed_singleton.isOpen_compl
  have hfnorm (v : Pt) (hv : v ≠ 0) : ‖f v‖ = 1 := by
    have hvp := norm_pos_iff.mpr hv
    simp [f, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp), ne_of_gt hvp]
  have hconv : Convex ℝ C := by
    intro v hv w hw a b ha hb hab
    intro m
    have hnrm : ‖a • v + b • w‖ ≤ a * ‖v‖ + b * ‖w‖ := by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] using norm_add_le (a • v) (b • w)
    have hmul := mul_le_mul_of_nonneg_left hnrm (h0 m)
    have hvw := add_le_add (mul_le_mul_of_nonneg_left (hv m) ha) (mul_le_mul_of_nonneg_left (hw m) hb)
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    nlinarith only [hmul, hvw]
  have hCclosed : IsClosed C := by
    have hc : IsClosed (⋂ m, {v : Pt | h m * ‖v‖ ≤ inner ℝ (n m) v}) := by
      apply isClosed_iInter
      intro m
      exact isClosed_le (continuous_const.mul continuous_norm) (continuous_const.inner continuous_id)
    convert hc using 1
    ext v
    simp [C]
  have hKC : ∀ u ∈ K, u ∈ C := by
    intro u hu m
    have hmu := Set.mem_iInter.mp hu m
    simpa [hmu.1] using hmu.2
  have hnK : ∀ u ∈ K, ‖u‖ = 1 := by
    intro u hu
    exact (Set.mem_iInter.mp hu ⟨0, hN⟩).1
  have hNmap : Continuous (fun v : P => f (v : Pt)) := by
    exact (continuous_subtype_val.norm.inv₀ (fun v => norm_ne_zero_iff.mpr v.property)).smul continuous_subtype_val
  let fs : P → Metric.sphere (0 : Pt) 1 := fun v => ⟨f v, by simpa [Metric.mem_sphere, dist_zero_right] using hfnorm v v.property⟩
  have hfs : Continuous fs := hNmap.subtype_mk _
  obtain ⟨z, hz⟩ := Set.image_nonempty.mp hint
  have hznorm : ‖(z : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using z.property
  have hz0 : (z : Pt) ≠ 0 := by intro hh; simp [hh] at hznorm
  let zp : P := ⟨z, hz0⟩
  have hfzp : fs zp = z := by
    apply Subtype.ext
    simp [fs, zp, f, hznorm]
  let W := fs ⁻¹' interior ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' K)
  have hW : IsOpen W := hfs.isOpen_preimage _ isOpen_interior
  have hzW : zp ∈ W := by change fs zp ∈ interior ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' K); rw [hfzp]; exact hz
  have hO : IsOpen ((Subtype.val : P → Pt) '' W) := hP.isOpenMap_subtype_val _ hW
  have hOC : ((Subtype.val : P → Pt) '' W) ⊆ C := by
    rintro v ⟨vp, hvp, rfl⟩
    have hvI : fs vp ∈ interior ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' K) := hvp
    have hvpre : fs vp ∈ (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' K := interior_subset hvI
    have hvK : f (vp : Pt) ∈ K := hvpre
    intro m
    have hvh := (Set.mem_iInter.mp hvK m).2
    rw [show inner ℝ (n m) (f vp) = inner ℝ (n m) (vp : Pt) / ‖(vp : Pt)‖ by simp [f, real_inner_smul_right, div_eq_mul_inv, mul_comm]] at hvh
    exact (le_div_iff₀ (norm_pos_iff.mpr vp.property)).mp hvh
  have hCint : (interior C).Nonempty := by
    refine ⟨(z : Pt), interior_mono hOC ?_⟩
    rw [hO.interior_eq]
    exact ⟨zp, hzW, rfl⟩
  have hCeq : closure (interior C) = C := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hCint, hCclosed.closure_eq]
  have hmapint : ∀ v ∈ interior C ∩ P, f v ∈ sInterior K := by
    intro v hv
    have hv0 := hv.2
    have hvp := norm_pos_iff.mpr hv0
    let vs : Metric.sphere (0 : Pt) 1 := ⟨f v, by simpa [Metric.mem_sphere, dist_zero_right] using hfnorm v hv0⟩
    let G : Metric.sphere (0 : Pt) 1 → Pt := fun u => ‖v‖ • (u : Pt)
    have hG : Continuous G := (continuous_const : Continuous (fun _ : Metric.sphere (0 : Pt) 1 => ‖v‖)).smul continuous_subtype_val
    have hGvs : G vs = v := by
      simp [G, vs, f, smul_smul, ne_of_gt hvp]
    have hGU : IsOpen (G ⁻¹' interior C) := hG.isOpen_preimage _ isOpen_interior
    have hsub : G ⁻¹' interior C ⊆ (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' K := by
      intro u hu
      have huC : G u ∈ C := interior_subset hu
      have hunorm : ‖(u : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using u.property
      apply Set.mem_iInter.mpr
      intro m
      refine ⟨hunorm, ?_⟩
      have hum := huC m
      dsimp [G] at hum
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hvp, hunorm, mul_one, real_inner_smul_right] at hum
      rw [mul_comm (h m) ‖v‖] at hum
      exact le_of_mul_le_mul_left hum hvp
    refine ⟨vs, interior_mono hsub ?_, rfl⟩
    rw [hGU.interior_eq]
    change G vs ∈ interior C
    rw [hGvs]
    exact hv.1
  have hbasic := SphereGeom.Aux.CapIntersection.basic_properties N hN n h hn h0
  have hclosed : IsClosed K := hbasic.2.1.isClosed
  apply Set.Subset.antisymm
  · intro u hu
    have hu1 := hnK u hu
    have hu0 : u ≠ 0 := by intro hh; simp [hh] at hu1
    have huC : u ∈ closure (interior C) := by rw [hCeq]; exact hKC u hu
    have huCP : u ∈ closure (interior C ∩ P) := hP.closure_inter ⟨huC, hu0⟩
    have hfu : ContinuousAt f u := (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hu0)).smul continuous_id.continuousAt
    have hfcl := mem_closure_image hfu huCP
    have hfu_eq : f u = u := by simp [f, hu1]
    rw [hfu_eq] at hfcl
    apply closure_mono (show f '' (interior C ∩ P) ⊆ sInterior K from ?_) hfcl
    rintro w ⟨v, hv, rfl⟩
    exact hmapint v hv
  · apply closure_minimal _ hclosed
    rintro u ⟨us, hus, rfl⟩
    have hpre : us ∈ (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' K := interior_subset hus
    exact hpre
