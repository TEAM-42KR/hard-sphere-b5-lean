import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

private theorem bounds {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (γ : ℝ → F) (hγ : ContDiff ℝ 1 γ) (x ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ (∀ s ∈ Set.Ioo (x-δ) (x+δ), |‖deriv γ s‖-‖deriv γ x‖|≤ε) ∧
    ∀ s ∈ Set.Ioo (x-δ) (x+δ), ∀ t ∈ Set.Ioo (x-δ) (x+δ),
      (‖deriv γ x‖-ε)*|s-t|≤dist (γ s) (γ t) ∧ dist (γ s) (γ t)≤(‖deriv γ x‖+ε)*|s-t| := by
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp
    hγ.continuous_deriv_one.continuousAt ε hε
  have hbound : ∀ s ∈ Set.Ioo (x-δ) (x+δ), ‖deriv γ s-deriv γ x‖≤ε := by
    intro s hs
    have hdist : dist s x < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1,hs.2]
    have hh : ‖deriv γ s - deriv γ x‖ < ε := by
      simpa only [dist_eq_norm] using hclose hdist
    exact hh.le
  refine ⟨δ,hδ,?_,?_⟩
  · intro s hs
    exact (abs_norm_sub_norm_le (deriv γ s) (deriv γ x)).trans (hbound s hs)
  · intro s hs t ht
    let q : ℝ → F := fun u => γ u - u • deriv γ x
    have hq (u : ℝ) : HasDerivAt q (deriv γ u - deriv γ x) u := by
      have hh := ((hγ.differentiable (by norm_num)).differentiableAt.hasDerivAt).sub
        ((hasDerivAt_id u).smul_const (deriv γ x))
      convert hh using 1 <;> simp [q]
      funext z
      rfl
    have he := (convex_Ioo (x-δ) (x+δ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (hq u).hasDerivWithinAt) hbound ht hs
    change ‖(γ s-s • deriv γ x)-(γ t-t • deriv γ x)‖≤ε*‖s-t‖ at he
    have hsub : (γ s-s • deriv γ x)-(γ t-t • deriv γ x) =
      (γ s-γ t)-(s-t) • deriv γ x := by module
    rw [hsub, Real.norm_eq_abs] at he
    have hv : ‖(s-t) • deriv γ x‖ = |s-t| * ‖deriv γ x‖ := by simp only [norm_smul,Real.norm_eq_abs]
    have htri1 := norm_sub_le (γ s-γ t) ((s-t) • deriv γ x)
    have htri2 := norm_sub_le ((s-t) • deriv γ x) (γ s-γ t)
    have hnorm := norm_sub_norm_le (γ s-γ t) ((s-t) • deriv γ x)
    have hnorm2 := norm_sub_norm_le ((s-t) • deriv γ x) (γ s-γ t)
    have hflip : ‖(s-t) • deriv γ x - (γ s-γ t)‖ = ‖(γ s-γ t)-(s-t) • deriv γ x‖ := norm_sub_rev _ _
    rw [hflip] at hnorm2
    rw [hv] at hnorm hnorm2
    rw [dist_eq_norm]
    constructor <;> nlinarith

private theorem SphereGeom.Aux.ArcLength.local_metric_speed_bounds (γ : ℝ → E3) (hγ : ContDiff ℝ 1 γ) (x ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ (∀ s ∈ Set.Ioo (x-δ) (x+δ), |‖deriv γ s‖-‖deriv γ x‖|≤ε) ∧
    ∀ s ∈ Set.Ioo (x-δ) (x+δ), ∀ t ∈ Set.Ioo (x-δ) (x+δ),
      (‖deriv γ x‖-ε)*|s-t|≤dist (γ s) (γ t) ∧ dist (γ s) (γ t)≤(‖deriv γ x‖+ε)*|s-t| := by
  exact bounds γ hγ x ε hε

open MeasureTheory SphereGeom
open scoped NNReal ENNReal
noncomputable section

private theorem SphereGeom.Aux.ArcLength.regular_density_measure_sandwich
    (γ : ℝ → E3) (a b L U k : ℝ)
    (hL : 0 < L) (hU : 0 ≤ U) (hk : 0 ≤ k) (hkUL : k * U ≤ L)
    (hγ : Continuous γ)
    (hspeed : ∀ t ∈ Set.Icc a b, L ≤ ‖deriv γ t‖ ∧ ‖deriv γ t‖ ≤ U)
    (hbounds : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      L * |s - t| ≤ dist (γ s) (γ t) ∧ dist (γ s) (γ t) ≤ U * |s - t|)
    (S : Set ℝ) (hS : MeasurableSet S) (hSab : S ⊆ Set.Icc a b) :
    ENNReal.ofReal k * (∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖) ≤ arcMeasure (γ '' S) ∧
      ENNReal.ofReal k * arcMeasure (γ '' S) ≤
        ∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖ := by
  have hbi : ENNReal.ofReal L * volume S ≤ arcMeasure (γ '' S) ∧
      arcMeasure (γ '' S) ≤ ENNReal.ofReal U * volume S := by
    let l : ℝ≥0 := ⟨L, hL.le⟩
    let u : ℝ≥0 := ⟨U, hU⟩
    have hlcoe : (l : ℝ≥0∞) = ENNReal.ofReal L := ENNReal.coe_nnreal_eq l
    have hucoe : (u : ℝ≥0∞) = ENNReal.ofReal U := ENNReal.coe_nnreal_eq u
    have hlne : l ≠ 0 := by
      intro h
      have hz : L = 0 := congrArg (fun q : ℝ≥0 => (q : ℝ)) h
      exact hL.ne' hz
    have hlene : (l : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hlne
    have hu : LipschitzOnWith u γ S := by
      apply LipschitzOnWith.of_dist_le_mul
      intro s hs t ht
      change dist (γ s) (γ t) ≤ U * dist s t
      rw [Real.dist_eq]
      exact (hbounds s (hSab hs) t (hSab ht)).2
    have hupper : arcMeasure (γ '' S) ≤ ENNReal.ofReal U * volume S := by
      have h := hu.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
      rw [ENNReal.rpow_one, hausdorffMeasure_real, hucoe] at h
      exact h
    let f : S → E3 := fun t => γ t
    have hf : AntilipschitzWith l⁻¹ f := by
      apply AntilipschitzWith.of_le_mul_dist
      intro s t
      change dist (s : ℝ) (t : ℝ) ≤ (l⁻¹ : ℝ≥0) * dist (γ s) (γ t)
      rw [Real.dist_eq, NNReal.coe_inv]
      change |(s : ℝ) - (t : ℝ)| ≤ L⁻¹ * dist (γ s) (γ t)
      exact (le_inv_mul_iff₀ hL).2 (hbounds s (hSab s.property) t (hSab t.property)).1
    have hcoeimage : (Subtype.val : S → ℝ) '' Set.univ = S := by
      ext t
      simp
    have hparameter : (Measure.hausdorffMeasure 1 : Measure S) Set.univ = volume S := by
      have h := (isometry_subtype_coe (s := S)).hausdorffMeasure_image
        (Or.inl (by norm_num : (0 : ℝ) ≤ 1)) (Set.univ : Set S)
      rw [hcoeimage, hausdorffMeasure_real] at h
      exact h.symm
    have hfimage : f '' (Set.univ : Set S) = γ '' S := by
      ext y
      constructor
      · rintro ⟨s, _, rfl⟩
        exact ⟨s, s.property, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hs⟩, Set.mem_univ _, rfl⟩
    have h := hf.le_hausdorffMeasure_image (by norm_num : (0 : ℝ) ≤ 1)
      (Set.univ : Set S)
    rw [ENNReal.rpow_one, hparameter, hfimage] at h
    have hscaled := mul_le_mul_right h (l : ℝ≥0∞)
    rw [ENNReal.coe_inv hlne, ENNReal.mul_inv_cancel_left hlene ENNReal.coe_ne_top,
      hlcoe] at hscaled
    exact ⟨hscaled, hupper⟩
  have hdensityLower : ENNReal.ofReal L * volume S ≤
      ∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖ := by
    calc
      ENNReal.ofReal L * volume S = ∫⁻ (_ : ℝ) in S, ENNReal.ofReal L := by simp
      _ ≤ ∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖ := by
        apply lintegral_mono_ae
        exact (ae_restrict_mem hS).mono (fun t ht =>
          ENNReal.ofReal_le_ofReal (hspeed t (hSab ht)).1)
  have hdensityUpper : (∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖) ≤
      ENNReal.ofReal U * volume S := by
    calc
      (∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖) ≤
          ∫⁻ (_ : ℝ) in S, ENNReal.ofReal U := by
        apply lintegral_mono_ae
        exact (ae_restrict_mem hS).mono (fun t ht =>
          ENNReal.ofReal_le_ofReal (hspeed t (hSab ht)).2)
      _ = ENNReal.ofReal U * volume S := by simp
  have hkULenn : ENNReal.ofReal k * ENNReal.ofReal U ≤ ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_mul hk]
    exact ENNReal.ofReal_le_ofReal hkUL
  have hscaled : ENNReal.ofReal k * (ENNReal.ofReal U * volume S) ≤
      ENNReal.ofReal L * volume S := by
    rw [← mul_assoc]
    exact mul_le_mul_left hkULenn (volume S)
  exact ⟨(mul_le_mul_right hdensityUpper (ENNReal.ofReal k)).trans
      (hscaled.trans hbi.1),
    (mul_le_mul_right hbi.2 (ENNReal.ofReal k)).trans
      (hscaled.trans hdensityLower)⟩

open MeasureTheory

noncomputable section

private theorem SphereGeom.Aux.ArcLength.regular_local_measure_le
    (X : Type*) [MeasurableSpace X] [TopologicalSpace X]
    [CompactSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      μ.restrict U ≤ ν.restrict U) : μ ≤ ν := by
  classical
  choose U hUo hxU hUle using hlocal
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
    U hUo hcover
  have hlocalEq : ∀ x : X, (μ ⊓ ν).restrict (U x) = μ.restrict (U x) := by
    intro x
    have h := Measure.restrict_sInf_eq_sInf_restrict
      (m := ({μ, ν} : Set (Measure X)))
      (by simp : ({μ, ν} : Set (Measure X)).Nonempty)
      ((hUo x).measurableSet)
    simpa only [sInf_pair, Set.image_insert_eq, Set.image_singleton,
      inf_of_le_left (hUle x)] using h
  have hfinite : (μ ⊓ ν).restrict (⋃ x ∈ t, U x) = μ.restrict (⋃ x ∈ t, U x) :=
    Measure.restrict_biUnion_finset_congr.mpr (fun x _ => hlocalEq x)
  have hwhole : (⋃ x ∈ t, U x) = (Set.univ : Set X) :=
    Set.Subset.antisymm (Set.subset_univ _) ht
  rw [hwhole, Measure.restrict_univ, Measure.restrict_univ] at hfinite
  exact inf_eq_left.mp hfinite

open MeasureTheory SphereGeom Topology

private theorem SphereGeom.Aux.ArcLength.regular_measure_identity (γ : ℝ → E3) (a b : ℝ) (hγ : ContDiff ℝ 1 γ)
    (hreg : ∀ t ∈ Set.Icc a b, deriv γ t ≠ 0) (hinj : Set.InjOn γ (Set.Icc a b)) :
    arcMeasure.comap (fun t : Set.Icc a b => γ t) =
      (volume.withDensity (fun t : ℝ => ENNReal.ofReal ‖deriv γ t‖)).comap
        (Subtype.val : Set.Icc a b → ℝ) := by
  let f : Set.Icc a b → E3 := fun t => γ t
  let μ : Measure (Set.Icc a b) := (volume.withDensity (fun t : ℝ => ENNReal.ofReal ‖deriv γ t‖)).comap Subtype.val
  let ν : Measure (Set.Icc a b) := arcMeasure.comap f
  have hf : MeasurableEmbedding f :=
    (hγ.continuous.comp continuous_subtype_val).isClosedEmbedding
      (fun s t h => Subtype.ext (hinj s.property t.property h)) |>.measurableEmbedding
  have hv : MeasurableEmbedding (Subtype.val : Set.Icc a b → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hcomp (k : ℝ) (hk : 0 ≤ k) (hk1 : k<1) :
      ENNReal.ofReal k • μ ≤ ν ∧ ENNReal.ofReal k • ν ≤ μ := by
    have hlocal (x : Set.Icc a b) : ∃ U : Set (Set.Icc a b), IsOpen U ∧ x ∈ U ∧
        (ENNReal.ofReal k • μ).restrict U ≤ ν.restrict U ∧
        (ENNReal.ofReal k • ν).restrict U ≤ μ.restrict U := by
      let w : ℝ := ‖deriv γ x‖
      have hw : 0<w := norm_pos_iff.mpr (hreg x x.property)
      let ε : ℝ := w*(1-k)/4
      have hε : 0<ε := by dsimp [ε]; positivity
      have hL : 0<w-ε := by dsimp [ε]; nlinarith
      have hU : 0≤w+ε := by positivity
      have hsc : k*(w+ε) ≤ w-ε := by
        have hprod : 0≤ε*(1-k) := mul_nonneg hε.le (by linarith)
        dsimp [ε] at *
        nlinarith
      obtain ⟨δ,hδ,hspd,hmet⟩ := SphereGeom.Aux.ArcLength.local_metric_speed_bounds γ hγ x ε hε
      let U : Set (Set.Icc a b) := {s | dist (s:ℝ) x < δ/2}
      have hUo : IsOpen U := by
        exact (isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const)
      have hxU : x ∈ U := by dsimp [U]; simp; positivity
      have hinside (s : ℝ) (hs : s ∈ Set.Icc ((x:ℝ)-δ/2) ((x:ℝ)+δ/2)) :
          s ∈ Set.Ioo ((x:ℝ)-δ) ((x:ℝ)+δ) := by
        constructor <;> linarith [hs.1,hs.2]
      have hsand (T : Set (Set.Icc a b)) (hT : MeasurableSet T) (hTU : T ⊆ U) :
          ENNReal.ofReal k * μ T ≤ ν T ∧ ENNReal.ofReal k * ν T ≤ μ T := by
        let R : Set ℝ := Subtype.val '' T
        have hR : MeasurableSet R := hv.measurableSet_image' hT
        have hRI : R ⊆ Set.Icc ((x:ℝ)-δ/2) ((x:ℝ)+δ/2) := by
          rintro s ⟨s,hs,rfl⟩
          have hh : |(s:ℝ)-(x:ℝ)|<δ/2 := by
            have hu : dist (s:ℝ) (x:ℝ) < δ/2 := hTU hs
            simpa only [Real.dist_eq] using hu
          exact ⟨by linarith [(abs_lt.mp hh).1], by linarith [(abs_lt.mp hh).2]⟩
        have hspe : ∀ s ∈ Set.Icc ((x:ℝ)-δ/2) ((x:ℝ)+δ/2),
            w-ε≤‖deriv γ s‖ ∧ ‖deriv γ s‖≤w+ε := by
          intro s hs
          have hh := abs_le.mp (hspd s (hinside s hs))
          change ‖deriv γ s‖-w ≥ -ε ∧ ‖deriv γ s‖-w≤ε at hh
          constructor <;> linarith [hh.1,hh.2]
        have hmetric : ∀ s ∈ Set.Icc ((x:ℝ)-δ/2) ((x:ℝ)+δ/2),
            ∀ t ∈ Set.Icc ((x:ℝ)-δ/2) ((x:ℝ)+δ/2),
            (w-ε)*|s-t|≤dist (γ s) (γ t) ∧ dist (γ s) (γ t)≤(w+ε)*|s-t| := by
          intro s hs t ht
          exact hmet s (hinside s hs) t (hinside t ht)
        have hh := SphereGeom.Aux.ArcLength.regular_density_measure_sandwich γ
          ((x:ℝ)-δ/2) ((x:ℝ)+δ/2) (w-ε) (w+ε) k hL hU hk hsc hγ.continuous
          hspe hmetric R hR hRI
        have himage : γ '' R = f '' T := by
          dsimp only [R, f]
          rw [Set.image_image]
        change ENNReal.ofReal k *
          ((volume.withDensity (fun t : ℝ => ENNReal.ofReal ‖deriv γ t‖)).comap Subtype.val) T ≤
            (arcMeasure.comap f) T ∧ ENNReal.ofReal k * (arcMeasure.comap f) T ≤
              ((volume.withDensity (fun t : ℝ => ENNReal.ofReal ‖deriv γ t‖)).comap Subtype.val) T
        rw [hv.comap_apply, withDensity_apply _ hR, hf.comap_apply]
        rw [himage] at hh
        exact hh
      refine ⟨U,hUo,hxU,?_,?_⟩
      · apply Measure.le_iff.mpr
        intro T hT
        rw [Measure.restrict_apply hT, Measure.restrict_apply hT, Measure.smul_apply]
        exact (hsand (T∩U) (hT.inter hUo.measurableSet) Set.inter_subset_right).1
      · apply Measure.le_iff.mpr
        intro T hT
        rw [Measure.restrict_apply hT, Measure.restrict_apply hT, Measure.smul_apply]
        exact (hsand (T∩U) (hT.inter hUo.measurableSet) Set.inter_subset_right).2
    constructor
    · apply SphereGeom.Aux.ArcLength.regular_local_measure_le
      intro x
      obtain ⟨U,hUo,hxU,h1,h2⟩ := hlocal x
      exact ⟨U,hUo,hxU,h1⟩
    · apply SphereGeom.Aux.ArcLength.regular_local_measure_le
      intro x
      obtain ⟨U,hUo,hxU,h1,h2⟩ := hlocal x
      exact ⟨U,hUo,hxU,h2⟩
  have hμν : μ ≤ ν := by
    apply Measure.le_iff.mpr
    intro T hT
    apply ENNReal.le_of_forall_lt_one_mul_le
    intro k hk
    have hkt : k≠⊤ := ne_top_of_le_ne_top (by simp) hk.le
    have hkr : k.toReal<1 := by
      have hh := (ENNReal.toReal_lt_toReal hkt (by simp : (1:ENNReal)≠⊤)).mpr hk
      simpa using hh
    have hh := Measure.le_iff.mp (hcomp k.toReal ENNReal.toReal_nonneg hkr).1 T hT
    rw [Measure.smul_apply, ENNReal.ofReal_toReal hkt] at hh
    exact hh
  have hνμ : ν ≤ μ := by
    apply Measure.le_iff.mpr
    intro T hT
    apply ENNReal.le_of_forall_lt_one_mul_le
    intro k hk
    have hkt : k≠⊤ := ne_top_of_le_ne_top (by simp) hk.le
    have hkr : k.toReal<1 := by
      have hh := (ENNReal.toReal_lt_toReal hkt (by simp : (1:ENNReal)≠⊤)).mpr hk
      simpa using hh
    have hh := Measure.le_iff.mp (hcomp k.toReal ENNReal.toReal_nonneg hkr).2 T hT
    rw [Measure.smul_apply, ENNReal.ofReal_toReal hkt] at hh
    exact hh
  exact le_antisymm hνμ hμν

open MeasureTheory SphereGeom

theorem proof_SphereGeom_Aux_ArcLength_arcMeasure_image_regular (γ : ℝ → E3) (a b : ℝ) (hγ : ContDiff ℝ 1 γ)
    (hreg : ∀ t ∈ Set.Icc a b, deriv γ t ≠ 0) (hinj : Set.InjOn γ (Set.Icc a b))
    (S : Set ℝ) (hS : MeasurableSet S) (hSab : S ⊆ Set.Icc a b) :
    arcMeasure (γ '' S) = ∫⁻ t in S, ENNReal.ofReal ‖deriv γ t‖ := by
  let f : Set.Icc a b → E3 := fun t => γ t
  have hf : MeasurableEmbedding f :=
    (hγ.continuous.comp continuous_subtype_val).isClosedEmbedding
      (fun s t h => Subtype.ext (hinj s.property t.property h)) |>.measurableEmbedding
  have hv : MeasurableEmbedding (Subtype.val : Set.Icc a b → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have h := congrArg (fun μ : Measure (Set.Icc a b) => μ (Subtype.val ⁻¹' S))
    (SphereGeom.Aux.ArcLength.regular_measure_identity γ a b hγ hreg hinj)
  rw [hf.comap_apply, hv.comap_apply] at h
  have hvimage : (Subtype.val : Set.Icc a b → ℝ) '' (Subtype.val ⁻¹' S) = S := by
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact hu
    · intro ht
      exact ⟨⟨t,hSab ht⟩,ht,rfl⟩
  have hfimage : f '' (Subtype.val ⁻¹' S) = γ '' S := by
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t,ht,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,hSab ht⟩,ht,rfl⟩
  rw [hfimage, hvimage, withDensity_apply _ hS] at h
  exact h
