import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_BulkMatching
import HardSphereB5Lean.Theorems.Thm_SphereGeom_integral_dOmega_frame
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000

private def SolidGeom.CapPolar.rayGauge (a h t : ℝ) : ℝ := (h-a*Real.cos t)/Real.sin t

private lemma SolidGeom.CapPolar.rayGauge_hasDerivAt (a h t : ℝ) (ht : t ∈ Set.Ioo 0 Real.pi) :
    HasDerivAt (SolidGeom.CapPolar.rayGauge a h)
      ((a-h*Real.cos t)/(Real.sin t)^2) t := by
  have hs : Real.sin t ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  have hd := ((hasDerivAt_const t h).sub ((Real.hasDerivAt_cos t).const_mul a)).div
    (Real.hasDerivAt_sin t) hs
  have he : (((0-a*(-Real.sin t))*Real.sin t-(h-a*Real.cos t)*Real.cos t)/(Real.sin t)^2) =
      (a-h*Real.cos t)/(Real.sin t)^2 := by
    congr 1
    have hc := Real.sin_sq_add_cos_sq t
    linear_combination a*hc
  have hf : (((fun x : ℝ => h)-(fun y => a*Real.cos y))/Real.sin) =
      SolidGeom.CapPolar.rayGauge a h := rfl
  simpa only [hf,Pi.sub_apply,he] using hd

private lemma SolidGeom.CapPolar.rayGauge_strictMono (a h : ℝ) (hh : 0 < h) (ha : h < a) :
    StrictMonoOn (SolidGeom.CapPolar.rayGauge a h) (Set.Ioo 0 Real.pi) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0:ℝ) Real.pi)
  · exact ((continuous_const.sub (continuous_const.mul Real.continuous_cos)).continuousOn).div
      Real.continuous_sin.continuousOn (fun t ht => ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(SolidGeom.CapPolar.rayGauge_hasDerivAt a h t ht).deriv]
    apply div_pos
    · have hc := Real.cos_le_one t
      nlinarith
    · exact sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)

private lemma SolidGeom.CapPolar.ray_cap_iff (a b h ρ t : ℝ) (hh : 0 < h) (ha : h < a)
    (hρ : ρ ∈ Set.Ioo 0 Real.pi) (hroot : a*Real.cos ρ+b*Real.sin ρ=h)
    (ht : t ∈ Set.Icc 0 Real.pi) : h ≤ a*Real.cos t+b*Real.sin t ↔ t ≤ ρ := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0,Real.cos_zero,Real.sin_zero]
    simp only [mul_one,mul_zero,add_zero]
    exact iff_of_true ha.le hρ.1.le
  rcases eq_or_lt_of_le ht.2 with hπ | hπ
  · rw [hπ,Real.cos_pi,Real.sin_pi]
    constructor <;> intro h <;> nlinarith [hρ.2]
  have hsin := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hsinρ := Real.sin_pos_of_pos_of_lt_pi hρ.1 hρ.2
  have hr : SolidGeom.CapPolar.rayGauge a h ρ = b := by
    unfold SolidGeom.CapPolar.rayGauge
    apply (div_eq_iff (ne_of_gt hsinρ)).mpr
    linarith
  have hmono := SolidGeom.CapPolar.rayGauge_strictMono a h hh ha
  have hle : SolidGeom.CapPolar.rayGauge a h t ≤ b ↔ t ≤ ρ := by
    rw [← hr]
    exact hmono.le_iff_le ⟨h0,hπ⟩ hρ
  rw [← hle]
  unfold SolidGeom.CapPolar.rayGauge
  rw [div_le_iff₀ hsin]
  constructor <;> intro h <;> linarith

private lemma SolidGeom.CapPolar.polar_norm (e : Fin 3 → E3) (he : Orthonormal ℝ e) (t φ : ℝ) :
    ‖SolidGeom.CapPolar.polar e t φ‖ = 1 := by
  have hinner := orthonormal_iff_ite.mp he
  have hsq : ‖SolidGeom.CapPolar.polar e t φ‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold SolidGeom.CapPolar.polar
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,hinner]
    simp
    linear_combination (Real.sin t)^2*(Real.sin_sq_add_cos_sq φ)+(Real.sin_sq_add_cos_sq t)
  nlinarith [norm_nonneg (SolidGeom.CapPolar.polar e t φ)]

private lemma SolidGeom.CapPolar.winner_min (P : Profile) (φ : ℝ) :
    ∀ j : Fin 3, SolidGeom.CapPolar.radius P φ ≤ P.rho j φ := by
  unfold SolidGeom.CapPolar.radius SolidGeom.CapPolar.winner
  split_ifs with h0 h1
  · intro j
    fin_cases j
    · exact le_rfl
    · exact h0.1
    · exact h0.2
  · intro j
    fin_cases j
    · by_contra hn
      exact h0 ⟨(lt_of_not_ge hn).le,((lt_of_not_ge hn).le.trans h1)⟩
    · exact le_rfl
    · exact h1
  · have h21 : P.rho 2 φ ≤ P.rho 1 φ := (le_of_not_ge h1)
    intro j
    fin_cases j
    · by_contra hn
      exact h0 ⟨(lt_of_not_ge hn).le.trans h21,(lt_of_not_ge hn).le⟩
    · exact h21
    · exact le_rfl

private lemma SolidGeom.CapPolar.ray_membership (P : Profile) (t φ : ℝ)
    (ht : t ∈ Set.Icc 0 Real.pi) :
    SolidGeom.CapPolar.polar P.e t φ ∈ SolidGeom.CapPolar.caps P ↔
      t ≤ SolidGeom.CapPolar.radius P φ := by
  have hcap : ∀ j, P.height j ≤ inner ℝ (P.normal j) (SolidGeom.CapPolar.polar P.e t φ) ↔
      t ≤ P.rho j φ := by
    intro j
    let a := inner ℝ (P.normal j) (P.e 2)
    let b := Real.cos φ*inner ℝ (P.normal j) (P.e 0)+Real.sin φ*inner ℝ (P.normal j) (P.e 1)
    have hroot : a*Real.cos (P.rho j φ)+b*Real.sin (P.rho j φ)=P.height j := by
      have hr := P.ray_boundary j φ
      unfold SolidGeom.CapPolar.polar at hr
      simp only [inner_add_right,real_inner_smul_right] at hr
      dsimp [a,b]
      nlinarith [hr]
    have he := SolidGeom.CapPolar.ray_cap_iff a b (P.height j) (P.rho j φ) t
      (P.height_pos j) (P.pole_inside j) (P.rho_range j φ) hroot ht
    unfold SolidGeom.CapPolar.polar
    simp only [inner_add_right,real_inner_smul_right]
    convert he using 1 <;> dsimp [a,b] <;> ring
  simp only [SolidGeom.CapPolar.caps,Set.mem_setOf_eq,SolidGeom.CapPolar.polar_norm P.e P.frame,
    true_and,hcap]
  constructor
  · intro h
    exact h (SolidGeom.CapPolar.winner P φ)
  · intro h j
    exact h.trans (SolidGeom.CapPolar.winner_min P φ j)

private lemma SolidGeom.CapPolar.caps_measurable (P : Profile) : MeasurableSet (SolidGeom.CapPolar.caps P) := by
  have hc : IsClosed (SolidGeom.CapPolar.caps P) := by
    have he : SolidGeom.CapPolar.caps P = {u : E3 | ‖u‖=1} ∩ ⋂ j, {u | P.height j ≤ inner ℝ (P.normal j) u} := by
      ext u
      simp [SolidGeom.CapPolar.caps]
    rw [he]
    exact (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop))
  exact hc.measurableSet

private lemma SolidGeom.CapPolar.winner_measurable (P : Profile) : Measurable (SolidGeom.CapPolar.winner P) := by
  unfold SolidGeom.CapPolar.winner
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · exact (measurableSet_le (P.rho_continuous 0).measurable (P.rho_continuous 1).measurable).inter
      (measurableSet_le (P.rho_continuous 0).measurable (P.rho_continuous 2).measurable)
  · exact measurableSet_le (P.rho_continuous 1).measurable (P.rho_continuous 2).measurable

private lemma SolidGeom.CapPolar.sector_measurable (P : Profile) (j : Fin 3) :
    MeasurableSet (SolidGeom.CapPolar.sector P j) :=
  measurableSet_Icc.inter ((SolidGeom.CapPolar.winner_measurable P)
    (MeasurableSet.singleton j))

#print axioms SolidGeom.CapPolar.ray_membership

private lemma SolidGeom.CapPolar.polar_coordinates (P : Profile) (t φ : ℝ) :
    inner ℝ (P.e 0) (polar P.e t φ) = Real.sin t*Real.cos φ ∧
    inner ℝ (P.e 1) (polar P.e t φ) = Real.sin t*Real.sin φ ∧
    inner ℝ (P.e 2) (polar P.e t φ) = Real.cos t := by
  have he := orthonormal_iff_ite.mp P.frame
  have h00 : inner ℝ (P.e (0:Fin 3)) (P.e (0:Fin 3)) = 1 := by
    rw [he]
    exact if_pos rfl
  have h01 : inner ℝ (P.e (0:Fin 3)) (P.e (1:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (0:Fin 3) ≠ 1)
  have h02 : inner ℝ (P.e (0:Fin 3)) (P.e (2:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (0:Fin 3) ≠ 2)
  have h10 : inner ℝ (P.e (1:Fin 3)) (P.e (0:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (1:Fin 3) ≠ 0)
  have h11 : inner ℝ (P.e (1:Fin 3)) (P.e (1:Fin 3)) = 1 := by
    rw [he]
    exact if_pos rfl
  have h12 : inner ℝ (P.e (1:Fin 3)) (P.e (2:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (1:Fin 3) ≠ 2)
  have h20 : inner ℝ (P.e (2:Fin 3)) (P.e (0:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (2:Fin 3) ≠ 0)
  have h21 : inner ℝ (P.e (2:Fin 3)) (P.e (1:Fin 3)) = 0 := by
    rw [he]
    exact if_neg (by decide : (2:Fin 3) ≠ 1)
  have h22 : inner ℝ (P.e (2:Fin 3)) (P.e (2:Fin 3)) = 1 := by
    rw [he]
    exact if_pos rfl
  simp only [polar,inner_add_right,real_inner_smul_right,h00,h01,h02,h10,h11,h12,h20,h21,h22,mul_one,mul_zero,add_zero,zero_add]
  trivial

private lemma SolidGeom.CapPolar.exitPoint_mem (P : Profile) (φ : ℝ) : exitPoint P φ ∈ caps P := by
  apply (ray_membership P (radius P φ) φ
    ⟨(P.rho_range _ φ).1.le,(P.rho_range _ φ).2.le⟩).mpr
  exact le_rfl

private lemma SolidGeom.CapPolar.ray_equal_root (a b h r t : ℝ) (hh : 0 < h) (ha : h < a)
    (hr : r ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (hroot : a*Real.cos r+b*Real.sin r=h) :
    a*Real.cos t+b*Real.sin t=h ↔ t=r := by
  have hrG : rayGauge a h r = b := by
    unfold rayGauge
    apply (div_eq_iff (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2))).mpr
    linarith
  constructor
  · intro he
    have htG : rayGauge a h t = b := by
      unfold rayGauge
      apply (div_eq_iff (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))).mpr
      linarith
    exact (rayGauge_strictMono a h hh ha).injOn ht hr (htG.trans hrG.symm)
  · rintro rfl
    exact hroot

private lemma SolidGeom.CapPolar.active_exit_proof (P : Profile) (j : Fin 3) (φ : ℝ) :
    P.rho j φ = radius P φ ↔ P.height j = inner ℝ (P.normal j) (exitPoint P φ) := by
  let a := inner ℝ (P.normal j) (P.e 2)
  let b := Real.cos φ*inner ℝ (P.normal j) (P.e 0)+Real.sin φ*inner ℝ (P.normal j) (P.e 1)
  have hexp : ∀ t : ℝ, inner ℝ (P.normal j) (polar P.e t φ) = a*Real.cos t+b*Real.sin t := by
    intro t
    unfold polar
    simp only [inner_add_right,real_inner_smul_right]
    dsimp [a,b]
    ring
  have hroot : a*Real.cos (P.rho j φ)+b*Real.sin (P.rho j φ)=P.height j := by
    rw [← hexp]
    exact P.ray_boundary j φ
  have he := ray_equal_root a b (P.height j) (P.rho j φ) (radius P φ)
    (P.height_pos j) (P.pole_inside j) (P.rho_range j φ) (P.rho_range _ φ) hroot
  unfold exitPoint
  rw [hexp]
  exact ⟨fun h => (he.mpr h.symm).symm, fun h => (he.mp h.symm).symm⟩

private lemma SolidGeom.CapPolar.polar_azimuth_inj (P : Profile) (r s φ ψ : ℝ)
    (hr : r ∈ Set.Ioo 0 Real.pi) (hs : s ∈ Set.Ioo 0 Real.pi)
    (hφ : φ ∈ Set.Ico 0 (2*Real.pi)) (hψ : ψ ∈ Set.Ico 0 (2*Real.pi))
    (he : polar P.e r φ = polar P.e s ψ) : φ=ψ := by
  have hc0 := congrArg (fun u => inner ℝ (P.e 0) u) he
  have hc1 := congrArg (fun u => inner ℝ (P.e 1) u) he
  have hc2 := congrArg (fun u => inner ℝ (P.e 2) u) he
  rw [(polar_coordinates P r φ).1,(polar_coordinates P s ψ).1] at hc0
  rw [(polar_coordinates P r φ).2.1,(polar_coordinates P s ψ).2.1] at hc1
  rw [(polar_coordinates P r φ).2.2,(polar_coordinates P s ψ).2.2] at hc2
  have hrs : r=s := Real.injOn_cos ⟨hr.1.le,hr.2.le⟩ ⟨hs.1.le,hs.2.le⟩ hc2
  subst s
  have hz := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2)
  have hcos := (mul_left_cancel₀ hz hc0)
  have hsin := (mul_left_cancel₀ hz hc1)
  obtain ⟨k,hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hcos hsin)
  have hkm : (-1:ℝ)<(k:ℝ) := by nlinarith [hφ.1,hφ.2,hψ.1,hψ.2,Real.pi_pos]
  have hkp : (k:ℝ)<(1:ℝ) := by nlinarith [hφ.1,hφ.2,hψ.1,hψ.2,Real.pi_pos]
  have hm : (-1:ℤ)<k := by exact_mod_cast hkm
  have hp : k<(1:ℤ) := by exact_mod_cast hkp
  have hzero : k=0 := by omega
  rw [hzero] at hk
  simpa only [Int.cast_zero,mul_zero,sub_eq_zero] using hk

private lemma SolidGeom.CapPolar.exitPoint_inj_proof (P : Profile) :
    Set.InjOn (exitPoint P) (Set.Ico 0 (2*Real.pi)) := by
  intro φ hφ ψ hψ he
  exact polar_azimuth_inj P (radius P φ) (radius P ψ) φ ψ
    (P.rho_range _ φ) (P.rho_range _ ψ) hφ hψ he

open HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
private lemma SolidGeom.CapPolar.matching_dist_pos {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (j : Fin 3) : 0 < dist (c i) (c (o j)) := by
  have hh := P.height_pos j
  rw [hm.height_eq j] at hh
  linarith

private lemma SolidGeom.CapPolar.matching_labels {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (m : Fin 4) : m=i ∨ ∃ j : Fin 3, m=o j := by
  have hcover : ∀ i a b d m : Fin 4, a ≠ i → b ≠ i → d ≠ i → a ≠ b → a ≠ d → b ≠ d →
      m=i ∨ m=a ∨ m=b ∨ m=d := by decide
  have hc := hcover i (o 0) (o 1) (o 2) m (hm.label_ne 0) (hm.label_ne 1) (hm.label_ne 2)
    (fun h => (by decide : (0:Fin 3) ≠ 1) (hm.label_injective h))
    (fun h => (by decide : (0:Fin 3) ≠ 2) (hm.label_injective h))
    (fun h => (by decide : (1:Fin 3) ≠ 2) (hm.label_injective h))
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨0,h⟩
  · exact Or.inr ⟨1,h⟩
  · exact Or.inr ⟨2,h⟩

private lemma SolidGeom.CapPolar.matching_inner_ball {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (j : Fin 3) (u : E3) (hu : ‖u‖=1) :
    P.height j ≤ inner ℝ (P.normal j) u ↔ c i+u ∈ Metric.closedBall (c (o j)) 1 := by
  let d := dist (c i) (c (o j))
  let v := c (o j)-c i
  have hd := matching_dist_pos hm j
  have hn : ‖v‖^2=d^2 := by dsimp [v,d];rw [← dist_eq_norm,dist_comm]
  have hv : c i+u-c (o j) = u-v := by dsimp [v];abel
  have hsq : dist (c i+u) (c (o j))^2 = 1-2*inner ℝ v u+d^2 := by
    rw [dist_eq_norm,hv,norm_sub_sq_real,hu,hn]
    rw [real_inner_comm]
    ring
  rw [hm.height_eq j,hm.normal_eq j,real_inner_smul_left]
  change d/2 ≤ d⁻¹*inner ℝ v u ↔ dist (c i+u) (c (o j)) ≤ 1
  have he : d/2 ≤ d⁻¹*inner ℝ v u ↔ d^2/2 ≤ inner ℝ v u := by
    rw [show d⁻¹*inner ℝ v u = inner ℝ v u/d by ring,le_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  rw [he]
  constructor <;> intro h <;> nlinarith [dist_nonneg (x:=c i+u) (y:=c (o j))]

private lemma SolidGeom.CapPolar.matching_inner_sphere {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (j : Fin 3) (u : E3) (hu : ‖u‖=1) :
    P.height j = inner ℝ (P.normal j) u ↔ dist (c i+u) (c (o j))=1 := by
  let d := dist (c i) (c (o j))
  let v := c (o j)-c i
  have hd := matching_dist_pos hm j
  have hn : ‖v‖^2=d^2 := by dsimp [v,d];rw [← dist_eq_norm,dist_comm]
  have hv : c i+u-c (o j) = u-v := by dsimp [v];abel
  have hsq : dist (c i+u) (c (o j))^2 = 1-2*inner ℝ v u+d^2 := by
    rw [dist_eq_norm,hv,norm_sub_sq_real,hu,hn]
    rw [real_inner_comm]
    ring
  rw [hm.height_eq j,hm.normal_eq j,real_inner_smul_left]
  change d/2 = d⁻¹*inner ℝ v u ↔ dist (c i+u) (c (o j)) = 1
  have he : d/2 = d⁻¹*inner ℝ v u ↔ d^2/2 = inner ℝ v u := by
    rw [show d⁻¹*inner ℝ v u = inner ℝ v u/d by ring,eq_div_iff (ne_of_gt hd)]
    constructor <;> intro h <;> nlinarith
  rw [he]
  constructor <;> intro h <;> nlinarith [dist_nonneg (x:=c i+u) (y:=c (o j))]

private lemma SolidGeom.CapPolar.matching_patch_iff {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (u : E3) : u ∈ caps P ↔ c i+u ∈ patch c i := by
  constructor
  · rintro ⟨hu,hcaps⟩
    constructor
    · simpa only [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_left] using hu
    · simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left]
      intro m
      rcases matching_labels hm m with hmi | ⟨j,hmj⟩
      · rw [hmi]
        change dist (c i+u) (c i) ≤ 1
        simpa only [dist_eq_norm,add_sub_cancel_left,hu] using (le_rfl : (1:ℝ) ≤ 1)
      · rw [hmj]
        exact (matching_inner_ball hm j u hu).mp (hcaps j)
  · rintro ⟨hsi,hK⟩
    have hu : ‖u‖=1 := by simpa only [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_left] using hsi
    refine ⟨hu,?_⟩
    intro j
    apply (matching_inner_ball hm j u hu).mpr
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hK
    exact hK _

open HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore

private lemma AA_frame_decomposition (P : Profile) (u : E3) :
    u = (inner ℝ (P.e 0) u) • P.e 0 + (inner ℝ (P.e 1) u) • P.e 1 +
      (inner ℝ (P.e 2) u) • P.e 2 := by
  let B := basisOfOrthonormalOfCardEqFinrank P.frame (by simp :
    Fintype.card (Fin 3) = Module.finrank ℝ E3)
  have hB : ∀ k : Fin 3, B k = P.e k := fun k =>
    congrFun (coe_basisOfOrthonormalOfCardEqFinrank P.frame (by simp)) k
  have hs := B.sum_repr u
  have hc : ∀ k : Fin 3, B.repr u k = inner ℝ (P.e k) u := by
    intro k
    have h := congrArg (fun v => inner ℝ (P.e k) v) hs
    simpa [inner_sum, real_inner_smul_right, hB, orthonormal_iff_ite.mp P.frame,
      eq_comm] using h
  simpa [hc, hB, Fin.sum_univ_succ, add_assoc] using hs.symm

private lemma AA_boundary_polar (P : Profile) (j : Fin 3) (u : E3)
    (hu : ‖u‖ = 1) (hj : P.height j = inner ℝ (P.normal j) u) :
    ∃ t ∈ Set.Ioo 0 Real.pi, ∃ φ ∈ Set.Icc 0 (2*Real.pi), polar P.e t φ = u := by
  let z := inner ℝ (P.e 2) u
  have he := orthonormal_iff_ite.mp P.frame
  have hpp : inner ℝ (P.e 2) (P.e 2) = 1 := by simpa using he 2 2
  have hp : ‖P.e 2‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hpp
    nlinarith [norm_nonneg (P.e 2)]
  have hz : |z| ≤ 1 := by
    simpa [z, hp, hu] using abs_real_inner_le_norm (P.e 2) u
  have hz1 : z < 1 := by
    apply lt_of_le_of_ne (abs_le.mp hz).2
    intro hz1
    have hn : ‖u-P.e 2‖^2 = 0 := by
      rw [norm_sub_sq_real, hu, hp, real_inner_comm]
      change 1^2-2*z+1^2=0
      rw [hz1]
      ring
    have hue : u=P.e 2 := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
    rw [hue] at hj
    exact (ne_of_lt (P.pole_inside j)) hj
  have hzm : -1 < z := by
    apply lt_of_le_of_ne (abs_le.mp hz).1
    intro hzm
    have hn : ‖u+P.e 2‖^2 = 0 := by
      rw [norm_add_sq_real, hu, hp, real_inner_comm]
      change 1^2+2*z+1^2=0
      rw [← hzm]
      ring
    have hue : u= -(P.e 2) := add_eq_zero_iff_eq_neg.mp
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
    rw [hue, inner_neg_right] at hj
    linarith [P.height_pos j, P.pole_inside j]
  let t := Real.arccos z
  have ht : t ∈ Set.Ioo 0 Real.pi :=
    ⟨Real.arccos_pos.mpr hz1, Real.arccos_lt_pi.mpr hzm⟩
  have hct : Real.cos t = z := Real.cos_arccos hzm.le hz1.le
  have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  let x := inner ℝ (P.e 0) u
  let y := inner ℝ (P.e 1) u
  have hd : u=x • P.e 0+y • P.e 1+z • P.e 2 := AA_frame_decomposition P u
  have hnorm : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hxyz : x^2+y^2+z^2=1 := by
    have hn2 := congrArg (fun v : E3 => inner ℝ v v) hd
    have hc : inner ℝ (x • P.e 0+y • P.e 1+z • P.e 2)
        (x • P.e 0+y • P.e 1+z • P.e 2) = x^2+y^2+z^2 := by
      simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,he]
      simp [Fin.ext_iff]
      <;> ring
    rw [hc,hnorm] at hn2
    exact hn2.symm
  have hsq : x^2+y^2=(Real.sin t)^2 := by
    have htr := Real.sin_sq_add_cos_sq t
    rw [hct] at htr
    nlinarith [htr]
  let w : ℂ := ⟨x,y⟩
  have hwn : ‖w‖ = Real.sin t := by
    have hw2 : ‖w‖^2=x^2+y^2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [w, Complex.normSq_apply, pow_two]
    nlinarith [norm_nonneg w]
  have hc : Real.sin t*Real.cos (Complex.arg w)=x := by
    simpa [hwn,w] using Complex.norm_mul_cos_arg w
  have hs : Real.sin t*Real.sin (Complex.arg w)=y := by
    simpa [hwn,w] using Complex.norm_mul_sin_arg w
  have hangle : ∃ φ ∈ Set.Icc 0 (2*Real.pi), Real.sin t*Real.cos φ=x ∧ Real.sin t*Real.sin φ=y := by
    by_cases h0 : 0 ≤ Complex.arg w
    · exact ⟨Complex.arg w,⟨h0,by linarith [Complex.arg_le_pi w,Real.pi_pos]⟩,hc,hs⟩
    · refine ⟨Complex.arg w+2*Real.pi,⟨?_,?_⟩,?_,?_⟩
      · linarith [Complex.neg_pi_lt_arg w,Real.pi_pos]
      · linarith [lt_of_not_ge h0]
      · simpa only [Real.cos_add_two_pi] using hc
      · simpa only [Real.sin_add_two_pi] using hs
  obtain ⟨φ,hφ,hcos,hsin⟩ := hangle
  refine ⟨t,ht,φ,hφ,?_⟩
  unfold polar
  rw [hcos,hsin,hct]
  exact hd.symm

private lemma AA_boundary_exit (P : Profile) (j : Fin 3) (u : E3)
    (hu : u ∈ caps P) (hj : P.height j = inner ℝ (P.normal j) u) :
    ∃ φ ∈ activeAzimuth P j, exitPoint P φ=u := by
  obtain ⟨t,ht,φ,hφ,hpol⟩ := AA_boundary_polar P j u hu.1 hj
  have hle : t ≤ radius P φ := (ray_membership P t φ ⟨ht.1.le,ht.2.le⟩).mp
    (hpol.symm ▸ hu)
  let a := inner ℝ (P.normal j) (P.e 2)
  let b := Real.cos φ*inner ℝ (P.normal j) (P.e 0)+Real.sin φ*inner ℝ (P.normal j) (P.e 1)
  have hexp : ∀ v : ℝ, inner ℝ (P.normal j) (polar P.e v φ) = a*Real.cos v+b*Real.sin v := by
    intro v
    unfold polar
    simp only [inner_add_right,real_inner_smul_right]
    dsimp [a,b]
    ring
  have hroot : a*Real.cos (P.rho j φ)+b*Real.sin (P.rho j φ)=P.height j := by
    rw [← hexp]
    exact P.ray_boundary j φ
  have htr : t=P.rho j φ := (ray_equal_root a b (P.height j) (P.rho j φ) t
    (P.height_pos j) (P.pole_inside j) (P.rho_range j φ) ht hroot).mp
      (by rw [← hexp,hpol]; exact hj.symm)
  have hrad : t=radius P φ := le_antisymm hle (by rw [htr];exact winner_min P φ j)
  refine ⟨φ,⟨hφ,htr.symm.trans hrad⟩,?_⟩
  change polar P.e (radius P φ) φ=u
  rw [← hrad]
  exact hpol

theorem proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_active_patch_circle_image
    (P : Profile) (c : Fin 4 → E3) (i : Fin 4) (o : Fin 3 → Fin 4)
    (hm : BulkMatching P c i o) (j : Fin 3) :
    (fun φ => c i+exitPoint P φ) '' activeAzimuth P j = patch c i ∩ Metric.sphere (c (o j)) 1 := by
  ext x
  constructor
  · rintro ⟨φ,hφ,rfl⟩
    have hu := exitPoint_mem P φ
    exact ⟨(matching_patch_iff hm _).mp hu,
      (matching_inner_sphere hm j _ hu.1).mp ((active_exit_proof P j φ).mp hφ.2)⟩
  · intro hx
    let u := x-c i
    have hxu : c i+u=x := by dsimp [u]; abel
    have hu : u ∈ caps P := (matching_patch_iff hm u).mpr (hxu.symm ▸ hx.1)
    have hj : P.height j=inner ℝ (P.normal j) u :=
      (matching_inner_sphere hm j u hu.1).mpr (by simpa only [hxu, Metric.mem_sphere] using hx.2)
    obtain ⟨φ,hφ,he⟩ := AA_boundary_exit P j u hu hj
    refine ⟨φ,hφ,?_⟩
    change c i+exitPoint P φ=x
    rw [he,hxu]

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_active_patch_circle_image
