import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
noncomputable section
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped Classical RealInnerProductSpace
set_option maxHeartbeats 1500000

section

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem S5b_ConvexDisk_exists_homeomorph_closedBall {s : Set E}
    (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hint : (interior s).Nonempty) :
    Nonempty (s ≃ₜ Metric.closedBall (0 : E) 1) := by
  obtain ⟨e, _, hclosure, _⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      hconv hint hcomp.isBounded
  have himage : e '' s = Metric.closedBall (0 : E) 1 := by
    simpa only [hcomp.isClosed.closure_eq] using hclosure
  exact ⟨(e.image s).trans (Homeomorph.setCongr himage)⟩

end

open scoped RealInnerProductSpace

section

private theorem S5b_ConvexDisk_stereoInvFun_cap_convex
    (v a : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1)
    (h : ℝ) (hh : 0 < h) (hlead : 0 < h - inner ℝ a v) :
    Convex ℝ {z : (ℝ ∙ v)ᗮ |
      h ≤ inner ℝ a (stereoInvFun hv z : EuclideanSpace ℝ (Fin 3))} := by
  let V := (ℝ ∙ v)ᗮ
  have quad : ∀ z : V,
      h ≤ inner ℝ a (stereoInvFun hv z : EuclideanSpace ℝ (Fin 3)) ↔
      (h - inner ℝ a v) * ‖z‖ ^ 2 - 4 * inner ℝ a (z : EuclideanSpace ℝ (Fin 3)) +
        4 * (h + inner ℝ a v) ≤ 0 := by
    intro z
    have hd : 0 < ‖z‖ ^ 2 + 4 := by positivity
    rw [stereoInvFun_apply, inner_smul_right, inner_add_right,
      inner_smul_right, inner_smul_right, ← div_eq_inv_mul, le_div_iff₀ hd]
    constructor <;> intro hz <;> nlinarith
  have hsq : ConvexOn ℝ Set.univ (fun z : V => ‖z‖ ^ 2) := by
    exact (convexOn_univ_norm (E := V)).pow (fun z _ => norm_nonneg z) 2
  intro x hx y hy s t hs ht hst
  apply (quad (s • x + t • y)).2
  have hxq := (quad x).1 hx
  have hyq := (quad y).1 hy
  have hnorm : ‖s • x + t • y‖ ^ 2 ≤ s * ‖x‖ ^ 2 + t * ‖y‖ ^ 2 := by
    simpa only [smul_eq_mul] using hsq.2 (Set.mem_univ x) (Set.mem_univ y) hs ht hst
  have hlin : inner ℝ a ((s • x + t • y : V) : EuclideanSpace ℝ (Fin 3)) =
      s * inner ℝ a (x : EuclideanSpace ℝ (Fin 3)) +
        t * inner ℝ a (y : EuclideanSpace ℝ (Fin 3)) := by
    simp only [Submodule.coe_add, Submodule.coe_smul, inner_add_right, inner_smul_right]
  have hnorm' := mul_le_mul_of_nonneg_left hnorm (le_of_lt hlead)
  have hxq' := mul_nonpos_of_nonneg_of_nonpos hs hxq
  have hyq' := mul_nonpos_of_nonneg_of_nonpos ht hyq
  rw [hlin]
  nlinarith [hnorm', hxq', hyq']

end

open Set Metric
open scoped InnerProductSpace

section

private abbrev S5b_ConvexDisk_E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S5b_ConvexDisk_E2 := EuclideanSpace ℝ (Fin 2)

local instance : Fact (Module.finrank ℝ S5b_ConvexDisk_E3 = 2 + 1) := ⟨by simp [S5b_ConvexDisk_E3]⟩

private noncomputable def S5b_ConvexDisk_capsSphereHomeomorph (a : Fin 3 → S5b_ConvexDisk_E3) (h : Fin 3 → ℝ) :
    ({u : S5b_ConvexDisk_E3 | ‖u‖ = 1 ∧ ∀ j, h j ≤ inner ℝ (a j) u} : Set S5b_ConvexDisk_E3) ≃ₜ
      ({u : sphere (0 : S5b_ConvexDisk_E3) 1 | ∀ j, h j ≤ inner ℝ (a j) (u : S5b_ConvexDisk_E3)} : Set (sphere (0 : S5b_ConvexDisk_E3) 1)) where
  toFun u := ⟨⟨u.1, by simpa only [mem_sphere_zero_iff_norm] using u.2.1⟩, u.2.2⟩
  invFun u := ⟨u.1.1, ⟨by simpa only [mem_sphere_zero_iff_norm] using u.1.2, u.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

set_option maxHeartbeats 800000 in
 theorem sphericalCaps_chart_properties (a : Fin 3 → S5b_ConvexDisk_E3) (h : Fin 3 → ℝ)
    (hh : ∀ j, 0 < h j) (w : S5b_ConvexDisk_E3) (hw : ‖w‖ = 1)
    (hstrict : ∀ j, h j < inner ℝ (a j) w) :
    ∃ (v : sphere (0 : S5b_ConvexDisk_E3) 1) (K : Set S5b_ConvexDisk_E2),
      (v : S5b_ConvexDisk_E3) = -w ∧ IsCompact K ∧ (interior K).Nonempty ∧
      Nonempty (({u : S5b_ConvexDisk_E3 | ‖u‖ = 1 ∧ ∀ j, h j ≤ inner ℝ (a j) u} : Set S5b_ConvexDisk_E3) ≃ₜ K) ∧
      K = {z : S5b_ConvexDisk_E2 | ∀ j, h j ≤ inner ℝ (a j) ((stereographic' 2 v).symm z : S5b_ConvexDisk_E3)} := by
  classical
  letI : Fact (Module.finrank ℝ S5b_ConvexDisk_E3 = 2 + 1) := ⟨by simp [S5b_ConvexDisk_E3]⟩
  let v : sphere (0 : S5b_ConvexDisk_E3) 1 := ⟨-w, by simpa [mem_sphere_zero_iff_norm] using hw⟩
  let e := stereographic' 2 v
  let T : Set (sphere (0 : S5b_ConvexDisk_E3) 1) := {u | ∀ j, h j ≤ inner ℝ (a j) (u : S5b_ConvexDisk_E3)}
  let K : Set S5b_ConvexDisk_E2 := {z | ∀ j, h j ≤ inner ℝ (a j) (e.symm z : S5b_ConvexDisk_E3)}
  have hTsource : T ⊆ e.source := by
    intro u hu
    simp only [e, stereographic'_source, mem_compl_iff, mem_singleton_iff]
    intro huv
    have hu0 := hu 0
    have hs0 := hstrict 0
    have hh0 := hh 0
    rw [huv] at hu0
    change h 0 ≤ inner ℝ (a 0) (-w) at hu0
    rw [inner_neg_right] at hu0
    linarith
  have himage : e '' T = K := by
    rw [e.image_eq_target_inter_inv_preimage hTsource]
    simp only [e, stereographic'_target, univ_inter]
    rfl
  have hTclosed : IsClosed T := by
    have hTeq : T = ⋂ j, {u : sphere (0 : S5b_ConvexDisk_E3) 1 | h j ≤ inner ℝ (a j) (u : S5b_ConvexDisk_E3)} := by
      ext u
      simp [T]
    rw [hTeq]
    exact isClosed_iInter fun j => isClosed_le continuous_const ((innerSL ℝ (a j)).continuous.comp continuous_subtype_val)
  have hKcompact : IsCompact K := by
    rw [← himage]
    exact hTclosed.isCompact.image_of_continuousOn (e.continuousOn.mono hTsource)
  have heinv : Continuous e.symm := by
    have he := e.continuousOn_symm
    simpa only [e, stereographic'_target, continuousOn_univ] using he
  let O : Set S5b_ConvexDisk_E2 := {z | ∀ j, h j < inner ℝ (a j) (e.symm z : S5b_ConvexDisk_E3)}
  have hOopen : IsOpen O := by
    have hOeq : O = ⋂ j, {z : S5b_ConvexDisk_E2 | h j < inner ℝ (a j) (e.symm z : S5b_ConvexDisk_E3)} := by
      ext z
      simp [O]
    rw [hOeq]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const ((innerSL ℝ (a j)).continuous.comp (continuous_subtype_val.comp heinv))
  have hOK : O ⊆ K := by
    intro z hz j
    exact (hz j).le
  let ws : sphere (0 : S5b_ConvexDisk_E3) 1 := ⟨w, by simpa only [mem_sphere_zero_iff_norm] using hw⟩
  have hwsT : ws ∈ T := fun j => (hstrict j).le
  have hwsinv : e.symm (e ws) = ws := e.left_inv (hTsource hwsT)
  have hewsO : e ws ∈ O := by
    intro j
    rw [hwsinv]
    exact hstrict j
  have hKinterior : (interior K).Nonempty := by
    refine ⟨e ws, ?_⟩
    apply interior_mono hOK
    rw [hOopen.interior_eq]
    exact hewsO
  refine ⟨v, K, rfl, hKcompact, hKinterior, ?_, rfl⟩
  exact ⟨(S5b_ConvexDisk_capsSphereHomeomorph a h).trans (e.homeomorphOfImageSubsetSource hTsource himage)⟩

private theorem S5b_ConvexDisk_sphericalCaps_closedDisk (a : Fin 3 → S5b_ConvexDisk_E3) (h : Fin 3 → ℝ)
    (ha : ∀ j, a j ≠ 0) (hh : ∀ j, 0 < h j) (w : S5b_ConvexDisk_E3) (hw : ‖w‖ = 1)
    (hstrict : ∀ j, h j < inner ℝ (a j) w) :
    Nonempty (({u : S5b_ConvexDisk_E3 | ‖u‖ = 1 ∧ ∀ j, h j ≤ inner ℝ (a j) u} : Set S5b_ConvexDisk_E3) ≃ₜ
      Metric.closedBall (0 : S5b_ConvexDisk_E2) 1) := by
  classical
  obtain ⟨v, K, hvw, hcompact, hinterior, hhomeo, hKeq⟩ :=
    sphericalCaps_chart_properties a h hh w hw hstrict
  let V := (ℝ ∙ (v : S5b_ConvexDisk_E3))ᗮ
  let U : V ≃ₗᵢ[ℝ] S5b_ConvexDisk_E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr
  let hv : ‖(v : S5b_ConvexDisk_E3)‖ = 1 := norm_eq_of_mem_sphere v
  let C : Set V := {z | ∀ j, h j ≤ inner ℝ (a j) (stereoInvFun hv z : S5b_ConvexDisk_E3)}
  have hCconvex : Convex ℝ C := by
    intro x hx y hy s t hs ht hst j
    have hlead : 0 < h j - inner ℝ (a j) (v : S5b_ConvexDisk_E3) := by
      rw [hvw, inner_neg_right]
      linarith [hh j, hstrict j]
    exact S5b_ConvexDisk_stereoInvFun_cap_convex (v : S5b_ConvexDisk_E3) (a j) hv (h j) (hh j) hlead
      (hx j) (hy j) hs ht hst
  have hKpreimage : K = U.symm ⁻¹' C := by
    rw [hKeq]
    ext z
    have hformula : (stereographic' 2 v).symm z = stereoInvFun hv (U.symm z) := rfl
    change (∀ j, h j ≤ inner ℝ (a j) ((stereographic' 2 v).symm z : S5b_ConvexDisk_E3)) ↔
      ∀ j, h j ≤ inner ℝ (a j) (stereoInvFun hv (U.symm z) : S5b_ConvexDisk_E3)
    rw [hformula]
  have hKconvex : Convex ℝ K := by
    rw [hKpreimage]
    exact hCconvex.linear_preimage U.symm.toLinearEquiv.toLinearMap
  obtain ⟨f⟩ := S5b_ConvexDisk_exists_homeomorph_closedBall hKconvex hcompact hinterior
  obtain ⟨g⟩ := hhomeo
  exact ⟨g.trans f⟩

end

section
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}
private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_midpoint_strict (hc : IsPathConfig c X Y s) (i : Fin 4) :
    dist (midpoint ℝ (c 0) (c 1)) (c i) < 1 := by
  have h01 : dist (c 0) (c 1) ^ 2 = 1 := hc.q01
  have h02 : dist (c 0) (c 2) ^ 2 = 1 := hc.q02
  have h03 : dist (c 0) (c 3) ^ 2 = Y := hc.q03
  have h12 : dist (c 1) (c 2) ^ 2 = X := hc.q12
  have h13 : dist (c 1) (c 3) ^ 2 = 1 := hc.q13
  have hi : dist (c i) (c 0) ^ 2 + dist (c i) (c 1) ^ 2 < 2 := by
    fin_cases i
    · change dist (c 0) (c 0) ^ 2 + dist (c 0) (c 1) ^ 2 < 2
      simpa [h01] using (by norm_num : (1 : ℝ) < 2)
    · change dist (c 1) (c 0) ^ 2 + dist (c 1) (c 1) ^ 2 < 2
      simpa [dist_comm, h01] using (by norm_num : (1 : ℝ) < 2)
    · change dist (c 2) (c 0) ^ 2 + dist (c 2) (c 1) ^ 2 < 2
      simpa only [dist_comm (c 2) (c 0), dist_comm (c 2) (c 1), h02, h12] using
        (show 1 + X < 2 by linarith [hc.X_lt_one])
    · change dist (c 3) (c 0) ^ 2 + dist (c 3) (c 1) ^ 2 < 2
      simpa only [dist_comm (c 3) (c 0), dist_comm (c 3) (c 1), h03, h13] using
        (show Y + 1 < 2 by linarith [hc.Y_lt_one])
  have h := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
    (c i) (c 0) (c 1)
  rw [dist_comm (c i) (midpoint ℝ (c 0) (c 1))] at h
  nlinarith

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_positive_volume (hc : IsPathConfig c X Y s) : 0 < vol c Finset.univ := by
  let U : Set Pt := ⋂ i : Fin 4, Metric.ball (c i) 1
  have hU : IsOpen U := isOpen_iInter_of_finite fun i : Fin 4 => Metric.isOpen_ball
  have hMU : midpoint ℝ (c 0) (c 1) ∈ U := by
    simp only [U, Set.mem_iInter, Metric.mem_ball]
    exact S5b_HardSphereB5_Lean_Geometry_PathCore_midpoint_strict hc
  have hUK : U ⊆ body c Finset.univ := by
    intro x hx
    simpa only [body, Set.mem_iInter, Finset.mem_univ, forall_true_left,
      Metric.mem_closedBall] using (fun i => (Set.mem_iInter.mp hx i).le)
  have hKB : body c Finset.univ ⊆ Metric.closedBall (c 0) 1 := by
    intro x hx
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hx 0) (Finset.mem_univ 0)
  have hpos : 0 < volume (body c Finset.univ) :=
    (hU.measure_pos volume ⟨_, hMU⟩).trans_le (measure_mono hUK)
  have hfinite : volume (body c Finset.univ) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hKB) measure_closedBall_lt_top).ne
  exact ENNReal.toReal_pos hpos.ne' hfinite

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_strict_patch_point_of_contact (a z b k : Pt)
    (hza : dist z a = 1) (hzb : dist z b = 1)
    (hab0 : 0 < dist a b) (hab2 : dist a b < 2) (hzk : dist z k < 1) :
    ∃ x : Pt, dist x a = 1 ∧ dist x z < 1 ∧ dist x b < 1 ∧ dist x k < 1 := by
  let u := z - a
  let v := b - a
  let r := ‖v‖ ^ 2
  have hu : ‖u‖ = 1 := by simpa [u, dist_eq_norm] using hza
  have hv0 : 0 < ‖v‖ := by simpa only [v, dist_eq_norm] using (show 0 < dist b a by rw [dist_comm]; exact hab0)
  have hv2 : ‖v‖ < 2 := by simpa only [v, dist_eq_norm] using (show dist b a < 2 by rw [dist_comm]; exact hab2)
  have hr0 : 0 < r := sq_pos_of_pos hv0
  have hr4 : r < 4 := by dsimp [r]; nlinarith
  have huv : ‖u - v‖ = 1 := by
    have he : u - v = z - b := by dsimp [u, v]; abel
    simpa [he, dist_eq_norm] using hzb
  have hin : inner ℝ u v = r / 2 := by
    have h := norm_sub_sq_real u v
    rw [hu, huv] at h
    dsimp [r]
    nlinarith
  let f : ℝ → Pt := fun t => ‖u + t • v‖⁻¹ • (u + t • v)
  have hf0 : f 0 = u := by simp [f, hu]
  have hn0 : ‖u + (0 : ℝ) • v‖ ≠ 0 := by simp [hu]
  have hnum : Continuous (fun t : ℝ => u + t • v) := by fun_prop
  have hf : ContinuousAt f 0 :=
    (hnum.norm.continuousAt.inv₀ hn0).smul hnum.continuousAt
  have hzcont : ContinuousAt (fun t => dist (a + f t) z) 0 :=
    (continuousAt_const.add hf).dist continuousAt_const
  have hkcont : ContinuousAt (fun t => dist (a + f t) k) 0 :=
    (continuousAt_const.add hf).dist continuousAt_const
  have hz0 : dist (a + f 0) z < 1 := by simp [hf0, u]
  have hk0 : dist (a + f 0) k < 1 := by simpa [hf0, u] using hzk
  have hz := hzcont.eventually (Iio_mem_nhds hz0)
  have hk := hkcont.eventually (Iio_mem_nhds hk0)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (hz.and hk)
  let t := ε / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hte : dist t 0 < ε := by simpa [Real.dist_eq, abs_of_pos ht] using
    (show t < ε by dsimp [t]; linarith)
  have hclose := he hte
  have hsq : ‖u + t • v‖ ^ 2 = 1 + t * r + t ^ 2 * r := by
    rw [norm_add_sq_real, hu, real_inner_smul_right, hin, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    dsimp [r]
    ring
  have hn : 0 < ‖u + t • v‖ := by
    have hp1 : 0 < t * r := mul_pos ht hr0
    have hp2 : 0 ≤ t ^ 2 * r := mul_nonneg (sq_nonneg t) hr0.le
    nlinarith [norm_nonneg (u + t • v)]
  have hnlt : ‖u + t • v‖ < 1 + 2 * t := by
    have hp : 0 < (4 - r) * (t + t ^ 2) :=
      mul_pos (by linarith) (by nlinarith [sq_nonneg t])
    nlinarith [norm_nonneg (u + t • v)]
  have hfnorm : ‖f t‖ = 1 := by
    simp only [f, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  have hfv : inner ℝ (f t) v = (r / 2 + t * r) / ‖u + t • v‖ := by
    simp only [f, real_inner_smul_left, inner_add_left, real_inner_smul_left, hin]
    rw [real_inner_self_eq_norm_sq]
    dsimp [r]
    ring
  have hfvg : r / 2 < inner ℝ (f t) v := by
    rw [hfv]
    apply (lt_div_iff₀ hn).2
    have hh := mul_lt_mul_of_pos_left hnlt hr0
    nlinarith
  have hfb : ‖f t - v‖ < 1 := by
    have hh := norm_sub_sq_real (f t) v
    rw [hfnorm] at hh
    dsimp [r] at hfvg ⊢
    nlinarith
  refine ⟨a + f t, ?_, hclose.1, ?_, hclose.2⟩
  · simpa [dist_eq_norm] using hfnorm
  · have heq : a + f t - b = f t - v := by dsimp [v]; abel
    simpa [dist_eq_norm, heq] using hfb

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_strict_patch_witness (hc : IsPathConfig c X Y s) (i : Fin 4) :
    ∃ x : Pt, dist x (c i) = 1 ∧ ∀ j : Fin 4, j ≠ i → dist x (c j) < 1 := by
  have hh01 : dist (c 0) (c 1) ^ 2 = 1 := hc.q01
  have hh02 : dist (c 0) (c 2) ^ 2 = 1 := hc.q02
  have hh13 : dist (c 1) (c 3) ^ 2 = 1 := hc.q13
  have hh03 : dist (c 0) (c 3) ^ 2 = Y := hc.q03
  have hh12 : dist (c 1) (c 2) ^ 2 = X := hc.q12
  have h01 : dist (c 0) (c 1) = 1 := by nlinarith [hh01, dist_nonneg (x := c 0) (y := c 1)]
  have h02 : dist (c 0) (c 2) = 1 := by nlinarith [hh02, dist_nonneg (x := c 0) (y := c 2)]
  have h13 : dist (c 1) (c 3) = 1 := by nlinarith [hh13, dist_nonneg (x := c 1) (y := c 3)]
  have h03 : dist (c 0) (c 3) < 1 := by nlinarith [hh03, hc.Y_lt_one]
  have h12 : dist (c 1) (c 2) < 1 := by nlinarith [hh12, hc.X_lt_one]
  have hp03 : 0 < dist (c 0) (c 3) := by nlinarith [hh03, hc.Y_pos, dist_nonneg (x := c 0) (y := c 3)]
  have hp12 : 0 < dist (c 1) (c 2) := by nlinarith [hh12, hc.X_pos, dist_nonneg (x := c 1) (y := c 2)]
  fin_cases i
  · obtain ⟨x, hx, hz, hb, hk⟩ := S5b_HardSphereB5_Lean_Geometry_PathCore_strict_patch_point_of_contact (c 0) (c 1) (c 3) (c 2)
      (by simpa only [dist_comm] using h01) h13 hp03 (by linarith) h12
    refine ⟨x, hx, ?_⟩
    intro j hj
    fin_cases j <;> first | exact (hj rfl).elim | exact hz | exact hb | exact hk
  · obtain ⟨x, hx, hz, hb, hk⟩ := S5b_HardSphereB5_Lean_Geometry_PathCore_strict_patch_point_of_contact (c 1) (c 0) (c 2) (c 3)
      h01 h02 hp12 (by linarith) h03
    refine ⟨x, hx, ?_⟩
    intro j hj
    fin_cases j <;> first | exact (hj rfl).elim | exact hz | exact hb | exact hk
  · obtain ⟨x, hx, hz, hb, hk⟩ := S5b_HardSphereB5_Lean_Geometry_PathCore_strict_patch_point_of_contact (c 2) (c 0) (c 1) (c 3)
      h02 h01 (by simpa only [dist_comm] using hp12) (by simpa only [dist_comm] using (show dist (c 1) (c 2) < 2 by linarith)) h03
    refine ⟨x, hx, ?_⟩
    intro j hj
    fin_cases j <;> first | exact (hj rfl).elim | exact hz | exact hb | exact hk
  · obtain ⟨x, hx, hz, hb, hk⟩ := S5b_HardSphereB5_Lean_Geometry_PathCore_strict_patch_point_of_contact (c 3) (c 1) (c 0) (c 2)
      h13 (by simpa only [dist_comm] using h01)
      (by simpa only [dist_comm] using hp03) (by simpa only [dist_comm] using (show dist (c 0) (c 3) < 2 by linarith)) h12
    refine ⟨x, hx, ?_⟩
    intro j hj
    fin_cases j <;> first | exact (hj rfl).elim | exact hz | exact hb | exact hk

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_patch_area_pos_of_strict (i : Fin 4)
    (hw : ∃ x : Pt, dist x (c i) = 1 ∧ ∀ j : Fin 4, j ≠ i → dist x (c j) < 1) :
    0 < pArea c i Finset.univ := by
  obtain ⟨x, hxi, hxj⟩ := hw
  let f : Metric.sphere (0 : Pt) 1 → Pt := fun u => c i + (u : Pt)
  have hf : Continuous f := continuous_const.add continuous_subtype_val
  let U : Set Pt := ⋂ j : Fin 4, if j = i then Set.univ else Metric.ball (c j) 1
  have hU : IsOpen U := isOpen_iInter_of_finite fun j => by
    by_cases hji : j = i
    · simp [hji]
    · simpa [hji] using (Metric.isOpen_ball : IsOpen (Metric.ball (c j) 1))
  have hxu : x ∈ U := by
    simp only [U, Set.mem_iInter]
    intro j
    by_cases hji : j = i
    · simp [hji]
    · simp [hji, Metric.mem_ball, hxj j hji]
  let u : Metric.sphere (0 : Pt) 1 := ⟨x - c i, by simpa [Metric.mem_sphere, dist_eq_norm] using hxi⟩
  have hu : f u = x := by simp [f, u]
  have hopen : IsOpen (f ⁻¹' U) := hU.preimage hf
  have hpos : 0 < (volume : Measure Pt).toSphere (f ⁻¹' U) :=
    hopen.measure_pos _ ⟨u, by simpa only [Set.mem_preimage, hu] using hxu⟩
  have hsub : f ⁻¹' U ⊆ f ⁻¹' body c Finset.univ := by
    intro v hv
    simp only [Set.mem_preimage, body, Set.mem_iInter, Finset.mem_univ, forall_true_left,
      Metric.mem_closedBall]
    intro j
    by_cases hji : j = i
    · subst j
      have hvunit : ‖(v : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using v.property
      simpa [f, dist_eq_norm] using hvunit.le
    · have hvj := Set.mem_iInter.mp hv j
      simpa [hji, Metric.mem_ball] using (show dist (f v) (c j) ≤ 1 from
        (by simpa [hji, Metric.mem_ball] using hvj : dist (f v) (c j) < 1).le)
  have hclosed : IsClosed (body c Finset.univ) :=
    isClosed_iInter fun j => isClosed_iInter fun _ => Metric.isClosed_closedBall
  have hmeasure : sphereMeasure (c i) (body c Finset.univ) =
      (volume : Measure Pt).toSphere (f ⁻¹' body c Finset.univ) :=
    Measure.map_apply hf.measurable hclosed.measurableSet
  have harea : 0 < sphereMeasure (c i) (body c Finset.univ) := by
    rw [hmeasure]
    exact hpos.trans_le (measure_mono hsub)
  letI : IsFiniteMeasure (sphereMeasure (c i)) := by
    change IsFiniteMeasure (SphereGeom.sphereMeasure (c i))
    unfold SphereGeom.sphereMeasure
    infer_instance
  simp only [pArea, Finset.mem_univ, if_true]
  exact ENNReal.toReal_pos harea.ne' (measure_ne_top _ _)

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_active_patches (hc : IsPathConfig c X Y s) : ∀ i, 0 < pArea c i Finset.univ := by
  intro i
  exact S5b_HardSphereB5_Lean_Geometry_PathCore_patch_area_pos_of_strict i (S5b_HardSphereB5_Lean_Geometry_PathCore_strict_patch_witness hc i)

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_unit_ball_iff_cap (u v : Pt) (hu : ‖u‖ = 1) :
    ‖u - v‖ ≤ 1 ↔ ‖v‖ ^ 2 / 2 ≤ inner ℝ v u := by
  have he := norm_sub_sq_real u v
  rw [hu, real_inner_comm v u] at he
  constructor
  · intro hd
    have hsq : ‖u - v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (u - v)]
    nlinarith
  · intro hc
    nlinarith [norm_nonneg (u - v)]

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_patch_disk (hc : IsPathConfig c X Y s) (i : Fin 4) :
    Nonempty (patch c i ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  obtain ⟨x, hxi, hxj⟩ := S5b_HardSphereB5_Lean_Geometry_PathCore_strict_patch_witness hc i
  let w : Pt := x - c i
  let a : Fin 3 → Pt := fun j => c (i.succAbove j) - c i
  let h : Fin 3 → ℝ := fun j => ‖a j‖ ^ 2 / 2
  have hw : ‖w‖ = 1 := by simpa [w, dist_eq_norm] using hxi
  have hd : ∀ j, ‖w - a j‖ < 1 := by
    intro j
    have heq : w - a j = x - c (i.succAbove j) := by dsimp [w, a]; abel
    simpa only [heq, ← dist_eq_norm] using hxj _ (Fin.succAbove_ne i j)
  have ha : ∀ j, a j ≠ 0 := by
    intro j haj
    have hdj := hd j
    rw [haj, sub_zero, hw] at hdj
    exact (lt_irrefl (1 : ℝ)) hdj
  have hh : ∀ j, 0 < h j := by
    intro j
    have hp := norm_pos_iff.mpr (ha j)
    dsimp [h]
    positivity
  have hstrict : ∀ j, h j < inner ℝ (a j) w := by
    intro j
    have he := norm_sub_sq_real w (a j)
    rw [hw, real_inner_comm (a j) w] at he
    have hsq : ‖w - a j‖ ^ 2 < 1 := by nlinarith [hd j, norm_nonneg (w - a j)]
    dsimp [h]
    nlinarith
  obtain ⟨ecap⟩ := S5b_ConvexDisk_sphericalCaps_closedDisk a h ha hh w hw hstrict
  let S : Set Pt := {u | ‖u‖ = 1 ∧ ∀ j, h j ≤ inner ℝ (a j) u}
  let e : Pt ≃ₜ Pt := Homeomorph.addLeft (c i)
  have hmem : ∀ u : Pt, c i + u ∈ patch c i ↔ u ∈ S := by
    intro u
    constructor
    · rintro ⟨hsphere, hbody⟩
      have hun : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hsphere
      refine ⟨hun, ?_⟩
      intro j
      have hb : dist (c i + u) (c (i.succAbove j)) ≤ 1 := by
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hbody _) (Finset.mem_univ _)
      have heq : c i + u - c (i.succAbove j) = u - a j := by dsimp [a]; abel
      have hnorm : ‖u - a j‖ ≤ 1 := by simpa only [dist_eq_norm, heq] using hb
      exact (S5b_HardSphereB5_Lean_Geometry_PathCore_unit_ball_iff_cap u (a j) hun).1 hnorm
    · rintro ⟨hun, hcap⟩
      refine ⟨by simpa [Metric.mem_sphere, dist_eq_norm] using hun, ?_⟩
      simp only [Kset, body, Set.mem_iInter, Finset.mem_univ, forall_true_left,
        Metric.mem_closedBall]
      intro j
      by_cases hji : j = i
      · subst j
        simpa [dist_eq_norm] using hun.le
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
        have hnorm : ‖u - a k‖ ≤ 1 := (S5b_HardSphereB5_Lean_Geometry_PathCore_unit_ball_iff_cap u (a k) hun).2 (hcap k)
        have heq : c i + u - c j = u - a k := by dsimp [a]; rw [hk]; abel
        simpa only [dist_eq_norm, heq] using hnorm
  have himage : e '' S = patch c i := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hmem u).2 hu
    · intro hz
      refine ⟨z - c i, ?_, ?_⟩
      · apply (hmem (z - c i)).1
        simpa using hz
      · simp [e]
  exact ⟨((e.image S).trans (Homeomorph.setCongr himage)).symm.trans ecap⟩

private theorem S5b_HardSphereB5_Lean_Geometry_PathCore_positive_volume_active_patches_of_deps (hc : IsPathConfig c X Y s) :
    0 < vol c Finset.univ ∧ (∀ i, 0 < pArea c i Finset.univ) ∧
      ∀ i, Nonempty (patch c i ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  exact ⟨S5b_HardSphereB5_Lean_Geometry_PathCore_positive_volume hc, S5b_HardSphereB5_Lean_Geometry_PathCore_active_patches hc, S5b_HardSphereB5_Lean_Geometry_PathCore_patch_disk hc⟩
end

theorem proof_HardSphereB5_Lean_Geometry_PathCore_positive_volume_active_patches {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) :
    0 < vol c Finset.univ ∧ (∀ i, 0 < pArea c i Finset.univ) ∧
      ∀ i, Nonempty (patch c i ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  exact @S5b_HardSphereB5_Lean_Geometry_PathCore_positive_volume_active_patches_of_deps c X Y s hc

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_positive_volume_active_patches
