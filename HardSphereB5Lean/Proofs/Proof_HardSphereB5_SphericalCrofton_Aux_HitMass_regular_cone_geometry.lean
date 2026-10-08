import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
open Set NormedSpace

theorem proof_HardSphereB5_SphericalCrofton_Aux_HitMass_regular_cone_geometry (K : Set Pt) (hK : IsRegularRegionCrofton K) :
    let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}
    IsClosed C ∧ Convex ℝ C ∧ (∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C) ∧
      (interior C).Nonempty ∧
      (∀ u : Pt, ‖u‖ = 1 → (u ∈ frontier C ↔ u ∈ sFrontier K)) := by
  classical
  have htransport :
      let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}
      ∀ u : Pt, ‖u‖ = 1 → (u ∈ interior C ↔ u ∈ sInterior K) := by
    classical
    dsimp only
    let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}
    let P : Set Pt := {v | v ≠ 0}
    let f : Pt → Pt := fun v => ‖v‖⁻¹ • v
    have hP : IsOpen P := isClosed_singleton.isOpen_compl
    have hfnorm (v : Pt) (hv : v ≠ 0) : ‖f v‖ = 1 := by
      have hvp := norm_pos_iff.mpr hv
      simp [f, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp), ne_of_gt hvp]
    let T : Set (Metric.sphere (0 : Pt) 1) := Subtype.val ⁻¹' K
    have hsC : ∀ z : Metric.sphere (0 : Pt) 1, (z : Pt) ∈ C ↔ (z : Pt) ∈ K := by
      intro z
      have hznorm : ‖(z : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using z.property
      have hz0 : (z : Pt) ≠ 0 := by intro hh; simp [hh] at hznorm
      simp [C, hznorm, hz0]
    intro u hu
    have hu0 : u ≠ 0 := by intro hh; simp [hh] at hu
    let us : Metric.sphere (0 : Pt) 1 := ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu⟩
    constructor
    · intro huC
      have hO : IsOpen ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' interior C) :=
        isOpen_interior.preimage continuous_subtype_val
      have hOT : (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' interior C ⊆ T := by
        intro z hz
        exact (hsC z).mp (interior_subset hz)
      refine ⟨us, interior_mono hOT ?_, rfl⟩
      rw [hO.interior_eq]
      exact huC
    · rintro ⟨z, hz, hzu⟩
      have hNmap : Continuous (fun v : P => f (v : Pt)) :=
        (continuous_subtype_val.norm.inv₀ (fun v => norm_ne_zero_iff.mpr v.property)).smul continuous_subtype_val
      let fs : P → Metric.sphere (0 : Pt) 1 := fun v =>
        ⟨f v, by simpa [Metric.mem_sphere, dist_zero_right] using hfnorm v v.property⟩
      have hfs : Continuous fs := hNmap.subtype_mk _
      let up : P := ⟨u, hu0⟩
      have hfup : fs up = z := by
        apply Subtype.ext
        change f u = (z : Pt)
        simp [f, hu, hzu]
      let W := fs ⁻¹' interior T
      have hW : IsOpen W := hfs.isOpen_preimage _ isOpen_interior
      have huW : up ∈ W := by change fs up ∈ interior T; rw [hfup]; exact hz
      have hO : IsOpen ((Subtype.val : P → Pt) '' W) := hP.isOpenMap_subtype_val _ hW
      have hOC : ((Subtype.val : P → Pt) '' W) ⊆ C := by
        rintro v ⟨vp, hvp, rfl⟩
        have hvpre : fs vp ∈ T := interior_subset hvp
        exact Or.inr hvpre
      apply interior_mono hOC
      rw [hO.interior_eq]
      exact ⟨up, huW, rfl⟩
  dsimp only
  let C : Set Pt := {v | v = 0 ∨ normalize v ∈ K}
  have hzero : (0 : Pt) ∈ C := Or.inl rfl
  have hscale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C := by
    intro r hr v hv
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · subst r
      simpa using hzero
    · rcases hv with hv0 | hvK
      · simp [hv0, C]
      · exact Or.inr (by rwa [normalize_smul_of_pos hrpos])
  have hunit : ∀ u : Pt, ‖u‖ = 1 → (u ∈ C ↔ u ∈ K) := by
    intro u hu
    have hu0 : u ≠ 0 := by intro hh; simp [hh] at hu
    simp [C, hu0, normalize_eq_self_of_norm_eq_one hu]
  have hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C := by
    intro x hx y hy
    by_cases hx0 : x = 0
    · simpa [hx0] using hy
    by_cases hy0 : y = 0
    · simpa [hy0] using hx
    have hxK : normalize x ∈ K := hx.resolve_left hx0
    have hyK : normalize y ∈ K := hy.resolve_left hy0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    let u := normalize x
    let v := normalize y
    have hxu : ‖x‖ • u = x := norm_smul_normalize x
    have hyv : ‖y‖ • v = y := norm_smul_normalize y
    have huC : u ∈ C := (hunit u (norm_normalize hx0)).mpr hxK
    have hvC : v ∈ C := (hunit v (norm_normalize hy0)).mpr hyK
    by_cases huv : u = -v
    · have hvu : v = -u := by rw [huv]; simp
      by_cases hnorm : ‖y‖ ≤ ‖x‖
      · have heq : x + y = (‖x‖ - ‖y‖) • u := by
          calc
            x + y = ‖x‖ • u + ‖y‖ • v := congrArg₂ (· + ·) hxu.symm hyv.symm
            _ = (‖x‖ - ‖y‖) • u := by rw [hvu, smul_neg, sub_smul, sub_eq_add_neg]
        rw [heq]
        exact hscale (‖x‖ - ‖y‖) (sub_nonneg.mpr hnorm) u huC
      · have heq : x + y = (‖y‖ - ‖x‖) • v := by
          calc
            x + y = ‖x‖ • u + ‖y‖ • v := congrArg₂ (· + ·) hxu.symm hyv.symm
            _ = (‖y‖ - ‖x‖) • v := by rw [huv, smul_neg, sub_smul, sub_eq_add_neg]; abel
        rw [heq]
        exact hscale (‖y‖ - ‖x‖) (by linarith) v hvC
    · let d : ℝ := ‖x‖ + ‖y‖
      let t : ℝ := ‖y‖ / d
      have hd : 0 < d := by dsimp [d]; linarith
      have ht0 : 0 ≤ t := div_nonneg hypos.le hd.le
      have ht1 : t ≤ 1 := (div_le_one hd).mpr (by dsimp [d]; linarith)
      have hgc : normalize ((1 - t) • u + t • v) ∈ K :=
        hK.geodesically_convex u hxK v hyK huv t ⟨ht0, ht1⟩
      have hdt : d * t = ‖y‖ := by dsimp [t]; field_simp
      have hdone : d * (1 - t) = ‖x‖ := by dsimp [d] at *; nlinarith [hdt]
      have heq : x + y = d • ((1 - t) • u + t • v) := by
        rw [smul_add, smul_smul, smul_smul, hdone, hdt, hxu, hyv]
      exact Or.inr (by rw [heq, normalize_smul_of_pos hd]; exact hgc)
  have hconv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    exact hadd (a • x) (hscale a ha x hx) (b • y) (hscale b hb y hy)
  let P : Set Pt := {v | v ≠ 0}
  have hP : IsOpen P := isClosed_singleton.isOpen_compl
  have hf : ContinuousOn (normalize : Pt → Pt) P := by
    intro v hv
    exact ((continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hv)).smul
      continuous_id.continuousAt).continuousWithinAt
  have hCclosed : IsClosed C := by
    have hO := hf.isOpen_inter_preimage hP hK.isCompact.isClosed.isOpen_compl
    have heq : Cᶜ = P ∩ normalize ⁻¹' Kᶜ := by
      ext v
      simp [C, P, not_or]
    rw [← isOpen_compl_iff, heq]
    exact hO
  have hint : (interior C).Nonempty := by
    obtain ⟨u, hu⟩ := hK.interior_nonempty
    have hunorm : ‖u‖ = 1 := by
      obtain ⟨us, hus, rfl⟩ := hu
      simpa [Metric.mem_sphere, dist_zero_right] using us.property
    refine ⟨u, ?_⟩
    exact (htransport u hunorm).mpr hu
  refine ⟨hCclosed, hconv, hscale, hint, ?_⟩
  intro u hu
  let T : Set (Metric.sphere (0 : Pt) 1) := Subtype.val ⁻¹' K
  let us : Metric.sphere (0 : Pt) 1 := ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu⟩
  have hT : IsClosed T := hK.isCompact.isClosed.preimage continuous_subtype_val
  have hsfront : u ∈ sFrontier K ↔ us ∈ frontier T := by
    constructor
    · rintro ⟨z, hz, hzu⟩
      have heq : z = us := Subtype.ext hzu
      exact heq ▸ hz
    · intro hz
      exact ⟨us, hz, rfl⟩
  have hsint : u ∈ sInterior K ↔ us ∈ interior T := by
    constructor
    · rintro ⟨z, hz, hzu⟩
      have heq : z = us := Subtype.ext hzu
      exact heq ▸ hz
    · intro hz
      exact ⟨us, hz, rfl⟩
  have hi : u ∈ interior C ↔ us ∈ interior T :=
    (htransport u hu).trans hsint
  change (u ∈ frontier C ↔ u ∈ sFrontier K)
  rw [hCclosed.frontier_eq, hsfront, hT.frontier_eq]
  change (u ∈ C ∧ u ∉ interior C) ↔ ((u ∈ K) ∧ us ∉ interior T)
  rw [hunit u hu, hi]
