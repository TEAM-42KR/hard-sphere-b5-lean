import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Santalo_density_chain_rule_at
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_endpointsA
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_MovingArc_endpointsA_width
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_sigma_gram_data
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Geom_gram_projection
set_option autoImplicit false
set_option maxHeartbeats 1000000
open HardSphereB5.Lean HardSphereB5.SphericalCrofton SphereGeom
open HardSphereB5.SphericalCrofton.Aux.MovingArc

private theorem cross_norm_sq_native (a b : Pt) :
    ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - inner ℝ a b ^ 2 := by
  simp [SphereGeom.cross, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
    cross_apply, Fin.sum_univ_succ]
  ring

private theorem cross_inner_first (a b : Pt) : inner ℝ a (cross a b) = 0 := by
  simp [SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
  ring

private theorem cross_inner_second (a b : Pt) : inner ℝ b (cross a b) = 0 := by
  simp [SphereGeom.cross, PiLp.inner_apply, cross_apply, Fin.sum_univ_succ]
  ring

private theorem axisA_facts (D : Pt) (hoff : offAxis D) :
    D ≠ 0 ∧ ‖nAv D‖ = 1 ∧ rawA D ≠ 0 ∧
      inner ℝ (nAv D) (rawA D) = 0 := by
  have hD : D ≠ 0 := by
    intro hd
    exact hoff 0 (by simpa using hd)
  have hn : ‖nAv D‖ = 1 := by
    simp [nAv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg D),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hD)]
  have horth : inner ℝ (nAv D) (rawA D) = 0 := by
    simp only [rawA, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  have he : ‖(e : Pt)‖ = 1 := by simp [e]
  have hraw : rawA D ≠ 0 := by
    intro hr
    have heq : e = (inner ℝ (nAv D) e) • nAv D := sub_eq_zero.mp hr
    have hcoeff : inner ℝ (nAv D) e ≠ 0 := by
      intro hc
      rw [hc, zero_smul] at heq
      have hbad := congrArg norm heq
      rw [he, norm_zero] at hbad
      norm_num at hbad
    have hDaxis : D = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) • e := by
      calc
        D = (-‖D‖) • nAv D := by
          simp [nAv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hD)]
        _ = ((-‖D‖ * (inner ℝ (nAv D) e)⁻¹) * inner ℝ (nAv D) e) • nAv D := by
          rw [mul_assoc, inv_mul_cancel₀ hcoeff, mul_one]
        _ = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) •
            ((inner ℝ (nAv D) e) • nAv D) := by rw [smul_smul]
        _ = (-‖D‖ * (inner ℝ (nAv D) e)⁻¹) • e := by rw [← heq]
    exact hoff _ hDaxis
  exact ⟨hD, hn, hraw, horth⟩

private theorem frameProof (D : Pt) (hoff : offAxis D) : Orthonormal ℝ (EA D) := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  have hf : ‖unitDir (rawA D)‖ = 1 := by
    simp [unitDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (rawA D)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]
  have hnf : inner ℝ (nAv D) (unitDir (rawA D)) = 0 := by
    rw [unitDir, real_inner_smul_right, ho, mul_zero]
  have hc : ‖cross (nAv D) (unitDir (rawA D))‖ ^ 2 = 1 := by
    rw [cross_norm_sq_native, hn, hf, hnf]
    norm_num
  have hf0 : inner ℝ (unitDir (rawA D)) (cross (nAv D) (unitDir (rawA D))) = 0 :=
    cross_inner_second _ _
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [EA, real_inner_self_eq_norm_sq, hf, hc, hf0, real_inner_comm]

private theorem fullCircleImage (v₁ v₂ p : E3) (hv : Orthonormal ℝ ![v₁, v₂, p]) :
    circlePt 0 v₁ v₂ 1 '' Set.Icc (-Real.pi) Real.pi = greatCircle p := by
  let e : Fin 3 → E3 := ![v₁, v₂, p]
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range e) := by
    apply Eq.ge
    apply hv.linearIndependent.span_eq_top_of_card_eq_finrank
    simp [E3]
  let b : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk hv hspan
  have hb (i : Fin 3) : b i = e i := by simp [b, e]
  have hb0 : b 0 = v₁ := by simp [hb, e]
  have hb1 : b 1 = v₂ := by simp [hb, e]
  have hb2 : b 2 = p := by simp [hb, e]
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · have hc : circlePt 0 v₁ v₂ 1 t = b.repr.symm (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0]) := by
        rw [← b.sum_repr_symm]
        simp [Fin.sum_univ_succ, hb0, hb1, hb2, circlePt]
      rw [hc, b.repr.symm.norm_map]
      have hs : ‖(WithLp.toLp 2 ![Real.cos t, Real.sin t, 0] : E3)‖ ^ 2 = 1 := by
        simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Real.cos_sq_add_sin_sq]
      nlinarith [norm_nonneg (WithLp.toLp 2 ![Real.cos t, Real.sin t, 0] : E3)]
    · have h1 : inner ℝ p v₁ = 0 := by simpa [e] using hv.inner_eq_zero (show (2 : Fin 3) ≠ 0 by decide)
      have h2 : inner ℝ p v₂ = 0 := by simpa [e] using hv.inner_eq_zero (show (2 : Fin 3) ≠ 1 by decide)
      simp [circlePt, inner_add_right, inner_smul_right, h1, h2]
  · rintro ⟨hu, hup⟩
    have hpcoord : b.repr u 2 = 0 := by simpa [b.repr_apply_apply, hb2] using hup
    have hnorm : b.repr u 0 ^ 2 + b.repr u 1 ^ 2 = 1 := by
      have h : ‖b.repr u‖ ^ 2 = 1 := by rw [b.repr.norm_map, hu]; norm_num
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simpa [Fin.sum_univ_succ, hpcoord] using h
    let z : ℂ := ⟨b.repr u 0, b.repr u 1⟩
    have hzn : ‖z‖ = 1 := by
      have h : ‖z‖ ^ 2 = 1 := by
        rw [Complex.sq_norm]
        simpa [Complex.normSq, z, pow_two] using hnorm
      nlinarith [norm_nonneg z]
    have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; norm_num at hzn
    refine ⟨z.arg, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
    have hc : Real.cos z.arg = b.repr u 0 := by simpa [Complex.cos_arg hz, hzn, z]
    have hs : Real.sin z.arg = b.repr u 1 := by simpa [Complex.sin_arg, hzn, z]
    rw [circlePt, zero_add, one_smul, hc, hs]
    have h := b.sum_repr u
    simpa [Fin.sum_univ_succ, hb0, hb1, hb2, hpcoord] using h

private theorem frameTriple (D : Pt) (hoff : offAxis D) :
    Orthonormal ℝ ![EA D 0, EA D 1, nAv D] := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  have hf : ‖unitDir (rawA D)‖ = 1 := by
    simp [unitDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (rawA D)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]
  have hnf : inner ℝ (nAv D) (unitDir (rawA D)) = 0 := by
    rw [unitDir, real_inner_smul_right, ho, mul_zero]
  have hc : ‖cross (nAv D) (unitDir (rawA D))‖ ^ 2 = 1 := by
    rw [cross_norm_sq_native, hn, hf, hnf]
    norm_num
  have hf0 : inner ℝ (unitDir (rawA D)) (cross (nAv D) (unitDir (rawA D))) = 0 :=
    cross_inner_second _ _
  have hn0 : inner ℝ (nAv D) (cross (nAv D) (unitDir (rawA D))) = 0 :=
    cross_inner_first _ _
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [EA, real_inner_self_eq_norm_sq, hf, hn, hc, hf0, hn0, hnf, real_inner_comm]

private theorem movingA_radius (D : Pt) (hL : D ∈ LamC) :
    0 < rA D ∧ (rA D)^2 = 1-‖D‖^2/4 := by
  have hnorm : ‖D‖ ≤ 1 := by
    simpa [LamC, Metric.mem_closedBall] using hL.1
  have hn0 := norm_nonneg D
  have hp : 0 < 1-‖D‖^2/4 := by nlinarith
  exact ⟨by simpa [rA] using Real.sqrt_pos.2 hp,
    by simpa [rA] using Real.sq_sqrt hp.le⟩

private theorem movingA_full (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.u D '' Set.Icc (-Real.pi) Real.pi =
      {x : Pt | ‖x‖=1 ∧ ‖D+x‖=1} := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  rcases movingA_radius D hL with ⟨hrr, hrr2⟩
  have himg := fullCircleImage (EA D 0) (EA D 1) (nAv D) (frameTriple D hoff)
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    let y : Pt := circlePt 0 (EA D 0) (EA D 1) 1 t
    have hy : y ∈ greatCircle (nAv D) := by
      rw [← himg]
      exact ⟨t, ht, rfl⟩
    have hysq : ‖y‖^2=1 := by rw [hy.1]; norm_num
    have hDy : inner ℝ D y = 0 := by
      have h := hy.2
      rw [nAv, real_inner_smul_left, inner_neg_left] at h
      have hne : ‖D‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hD)
      exact (neg_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hne))
    have hchart : HardSphereB5.SphericalCrofton.Aux.MovingArc.u D t = HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D + rA D • y := by
      simp [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, circlePt, y]
    rw [hchart]
    have hsum : D+(HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D+rA D•y) = (1/2 : ℝ)•D+rA D•y := by
      simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.cA]
      module
    constructor
    · have hsq : ‖HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D+rA D•y‖^2=1 := by
        rw [norm_add_sq_real]
        simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, norm_smul, Real.norm_eq_abs, real_inner_smul_left,
          real_inner_smul_right, hDy]
        norm_num [abs_of_pos hrr]
        nlinarith [hrr2]
      nlinarith [norm_nonneg (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D+rA D•y)]
    · rw [hsum]
      have hsq : ‖(1/2:ℝ)•D+rA D•y‖^2=1 := by
        rw [norm_add_sq_real]
        simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left,
          real_inner_smul_right, hDy]
        norm_num [abs_of_pos hrr]
        nlinarith [hrr2]
      nlinarith [norm_nonneg ((1/2:ℝ)•D+rA D•y)]
  · rintro ⟨hx, hDx⟩
    have hDxsq := norm_add_sq_real D x
    rw [hx, hDx] at hDxsq
    have hinner : inner ℝ D x = -(‖D‖^2)/2 := by nlinarith
    let y : Pt := (rA D)⁻¹ • (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)
    have hDy : inner ℝ D (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) = 0 := by
      rw [inner_sub_right, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right, real_inner_self_eq_norm_sq, hinner]
      ring
    have hyperp : inner ℝ (nAv D) y = 0 := by
      change inner ℝ (‖D‖⁻¹ • (-D)) ((rA D)⁻¹ • (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)) = 0
      rw [real_inner_smul_left, real_inner_smul_right, inner_neg_left, hDy]
      ring
    have hxcsq : ‖x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D‖^2 = (rA D)^2 := by
      rw [norm_sub_sq_real, hx, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right,
        ← real_inner_comm x D, hinner, norm_smul]
      norm_num
      nlinarith [hrr2]
    have hxc : ‖x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D‖=rA D := by
      nlinarith [norm_nonneg (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)]
    have hynorm : ‖y‖=1 := by
      change ‖(rA D)⁻¹ • (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrr, hxc,
        inv_mul_cancel₀ hrr.ne']
    have hy : y ∈ greatCircle (nAv D) := ⟨hynorm, hyperp⟩
    rw [← himg] at hy
    rcases hy with ⟨t, ht, hty⟩
    refine ⟨t, ht, ?_⟩
    have hchart : HardSphereB5.SphericalCrofton.Aux.MovingArc.u D t = HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D + rA D •
        (circlePt 0 (EA D 0) (EA D 1) 1 t) := by
      simp [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, circlePt]
    rw [hchart, hty]
    simp [y, smul_smul, mul_inv_cancel₀ hrr.ne']

private theorem cutBoundsProof (D : Pt) (hL : D ∈ LamC) (hoff : offAxis D)
    (hRc : Rc ‖D‖ ‖D - e‖ < 1) : 0 < cutA D ∧ cutA D < 1 := by
  let a : ℝ := ‖D‖
  let b : ℝ := ‖D - e‖
  let t : ℝ := inner ℝ D e
  let K : ℝ := a ^ 2 - t ^ 2
  let H : ℝ := (a + b + 1) * (a + b - 1) * (a - b + 1) * (-a + b + 1)
  have he : ‖e‖ = (1 : ℝ) := by simp [e]
  have hD : D ≠ 0 := by simpa using (hoff 0)
  have hDe : D - e ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa using (hoff 1)
  have ha : 0 < a := norm_pos_iff.mpr hD
  have hb : 0 < b := norm_pos_iff.mpr hDe
  have hnorms : a ≤ 1 ∧ b ≤ 1 := by
    simpa [LamC, Metric.mem_closedBall, dist_eq_norm, a, b] using hL
  have ha2 : a ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ ha.le (by norm_num : (0 : ℝ) ≤ 1)).2 hnorms.1
  have hb_sq : b ^ 2 = a ^ 2 - 2 * t + 1 := by
    have hh := norm_sub_sq_real D e
    rw [he] at hh
    simpa only [one_pow] using hh
  have ht : t < 1 := by
    have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
    nlinarith only [hb_sq, ha2, hb2]
  have hproj : ‖D - t • e‖ ^ 2 = K := by
    have hi : inner ℝ D (t • e) = t ^ 2 := by
      rw [inner_smul_right]
      change t * t = t ^ 2
      ring
    have hn : ‖t • e‖ ^ 2 = t ^ 2 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
    have hh := norm_sub_sq_real D (t • e)
    rw [hi, hn] at hh
    change ‖D - t • e‖ ^ 2 = a ^ 2 - 2 * t ^ 2 + t ^ 2 at hh
    dsimp [K]
    nlinarith only [hh]
  have hK : 0 < K := by
    rw [← hproj]
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hoff t)))
  have hH : H = 4 * K := by
    calc
      H = 4 * a ^ 2 - (a ^ 2 + 1 - b ^ 2) ^ 2 := by dsimp [H]; ring
      _ = 4 * K := by rw [hb_sq]; dsimp [K]; ring
  have hHpos : 0 < H := by rw [hH]; positivity
  have hRC : a * b < Real.sqrt H := by
    change a * b / Real.sqrt H < 1 at hRc
    have hh := (div_lt_iff₀ (Real.sqrt_pos.2 hHpos)).mp hRc
    simpa only [one_mul] using hh
  have hRCsq : a ^ 2 * b ^ 2 < 4 * K := by
    have hh := (sq_lt_sq₀ (mul_pos ha hb).le (Real.sqrt_nonneg H)).2 hRC
    rw [mul_pow, Real.sq_sqrt hHpos.le, hH] at hh
    exact hh
  let n : Pt := nAv D
  let s : ℝ := inner ℝ n e
  have hnn : ‖n‖ = 1 := by
    dsimp [n, nAv]
    rw [norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
    exact inv_mul_cancel₀ ha.ne'
  have hs : s = -(t / a) := by
    dsimp [s, n, nAv]
    rw [inner_smul_left, inner_neg_left]
    change a⁻¹ * -t = -(t / a)
    ring
  have hraw_def : rawA D = e - s • n := rfl
  have hrawnorm : ‖rawA D‖ ^ 2 = 1 - s ^ 2 := by
    have hi : inner ℝ e (s • n) = s ^ 2 := by
      rw [inner_smul_right, real_inner_comm n e]
      change s * s = s ^ 2
      ring
    have hn : ‖s • n‖ ^ 2 = s ^ 2 := by
      rw [norm_smul, hnn, mul_one, Real.norm_eq_abs, sq_abs]
    have hh := norm_sub_sq_real e (s • n)
    rw [← hraw_def, he, hi, hn] at hh
    nlinarith only [hh]
  have hrawsq : a ^ 2 * ‖rawA D‖ ^ 2 = K := by
    rw [hrawnorm, hs]
    dsimp [K]
    field_simp [ha.ne']
    <;> ring
  have hrawpos : 0 < ‖rawA D‖ := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro hh
    have hz : ‖rawA D‖ = 0 := hh.symm
    rw [hz] at hrawsq
    norm_num at hrawsq
    linarith only [hrawsq, hK]
  have hrarg : 0 < 1 - a ^ 2 / 4 := by linarith only [ha2]
  have hr : 0 < rA D := Real.sqrt_pos.2 hrarg
  have hrsq : rA D ^ 2 = 1 - a ^ 2 / 4 := Real.sq_sqrt hrarg.le
  let den : ℝ := 2 * rA D * ‖rawA D‖
  have hden : 0 < den := by dsimp [den]; positivity
  have hdensq : a ^ 2 * den ^ 2 = (4 - a ^ 2) * K := by
    calc
      a ^ 2 * den ^ 2 = 4 * rA D ^ 2 * (a ^ 2 * ‖rawA D‖ ^ 2) := by dsimp [den]; ring
      _ = (4 - a ^ 2) * K := by rw [hrsq, hrawsq]; ring
  have hgap : a ^ 2 * (den ^ 2 - (1 - t) ^ 2) = 4 * K - a ^ 2 * b ^ 2 := by
    rw [mul_sub, hdensq, hb_sq]
    dsimp [K]
    ring
  have hprodpos : 0 < a ^ 2 * (den ^ 2 - (1 - t) ^ 2) := by
    rw [hgap]
    linarith only [hRCsq]
  have hg : (1 - t) ^ 2 < den ^ 2 := by
    by_contra hh
    have hh' : den ^ 2 - (1 - t) ^ 2 ≤ 0 := by linarith only [le_of_not_gt hh]
    have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hh'
    linarith only [hm, hprodpos]
  have hnum : 0 < 1 - t := sub_pos.mpr ht
  have hlt : 1 - t < den := (sq_lt_sq₀ hnum.le hden.le).mp hg
  change 0 < (1 - t) / den ∧ (1 - t) / den < 1
  exact ⟨div_pos hnum hden, (div_lt_iff₀ hden).mpr (by simpa using hlt)⟩

private theorem circleBandProof (c : E3) (E : Fin 2 → E3) (he : Orthonormal ℝ E)
    (r : ℝ) (hr : 0 < r) (k : ℝ) (hklo : -1 ≤ k) (hkhi : k ≤ 1) :
    circlePt c (E 0) (E 1) r '' Set.Icc (-Real.arccos k) (Real.arccos k) =
      {x | x ∈ circlePt c (E 0) (E 1) r '' Set.Icc (-Real.pi) Real.pi ∧
        r * k ≤ inner ℝ (E 0) (x - c)} := by
  have hcoord (t : ℝ) :
      inner ℝ (E 0) (circlePt c (E 0) (E 1) r t - c) = r * Real.cos t := by
    simp [circlePt, inner_add_right, inner_smul_right, orthonormal_iff_ite.mp he, he.norm_eq_one]
  have htrig (t : ℝ) (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
      k ≤ Real.cos t ↔ t ∈ Set.Icc (-Real.arccos k) (Real.arccos k) := by
    have ht_abs : |t| ≤ Real.pi := abs_le.mpr ht
    have hm : Real.cos (Real.arccos k) ≤ Real.cos |t| ↔ |t| ≤ Real.arccos k :=
      Real.strictAntiOn_cos.le_iff_ge
        ⟨Real.arccos_nonneg k, Real.arccos_le_pi k⟩ ⟨abs_nonneg t, ht_abs⟩
    simpa only [Real.cos_arccos hklo hkhi, Real.cos_abs, abs_le, Set.mem_Icc] using hm
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hfull : t ∈ Set.Icc (-Real.pi) Real.pi :=
      ⟨by linarith [ht.1, Real.arccos_le_pi k], by linarith [ht.2, Real.arccos_le_pi k]⟩
    refine ⟨⟨t, hfull, rfl⟩, ?_⟩
    rw [hcoord]
    exact mul_le_mul_of_nonneg_left ((htrig t hfull).mpr ht) hr.le
  · rintro ⟨⟨t, ht, rfl⟩, hcut⟩
    rw [hcoord] at hcut
    exact ⟨t, (htrig t ht).mp (le_of_mul_le_mul_left hcut hr), rfl⟩

private theorem arcAProof (D : Pt)
  (hL : D ∈ LamC) (hoff : offAxis D) (hRc : Rc ‖D‖ ‖D-e‖ < 1) :
  arcA D = HardSphereB5.SphericalCrofton.Aux.MovingArc.u D '' Set.Icc (-(halfA D)) (halfA D) := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  rcases movingA_radius D hL with ⟨hrr, hrr2⟩
  rcases cutBoundsProof D hL hoff hRc with ⟨hcut0, hcut1⟩
  have hrn : 0 < ‖rawA D‖ := norm_pos_iff.mpr hr
  have hrn2 : 0 < 2*‖rawA D‖ := by positivity
  have hcutR : rA D * cutA D = (1-inner ℝ D e)/(2*‖rawA D‖) := by
    rw [cutA]
    field_simp [hrr.ne', hrn.ne'] <;> ring
  have hchar (x : Pt) (hx : ‖x‖=1) (hDx : ‖D+x‖=1) :
      ‖D+x-e‖≤1 ↔ rA D * cutA D ≤
        inner ℝ (EA D 0) (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) := by
    have hDxsq := norm_add_sq_real D x
    rw [hx, hDx] at hDxsq
    have hinner : inner ℝ D x = -(‖D‖^2)/2 := by nlinarith
    have hperp : inner ℝ (nAv D) (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)=0 := by
      simp only [nAv, inner_sub_right, real_inner_smul_left, inner_neg_left,
        HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hinner]
      ring
    have hproj : ‖rawA D‖ * inner ℝ (EA D 0)
        (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) =
          inner ℝ e (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) := by
      change ‖rawA D‖ * inner ℝ (‖rawA D‖⁻¹ • rawA D) _ = _
      rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hrn.ne', one_mul,
        rawA, inner_sub_left, real_inner_smul_left, hperp, mul_zero, sub_zero]
    have hlin : ‖rawA D‖ * inner ℝ (EA D 0)
        (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) = inner ℝ x e + inner ℝ D e/2 := by
      rw [hproj, inner_sub_right, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, real_inner_smul_right,
        real_inner_comm x e, real_inner_comm D e]
      ring
    have hesq : ‖(e : Pt)‖=1 := by simp [e]
    have hnorm := norm_sub_sq_real (D+x) e
    rw [hDx, hesq, inner_add_left] at hnorm
    rw [hcutR, div_le_iff₀ hrn2]
    constructor
    · intro hb
      have hb2 : ‖D+x-e‖^2≤1 := by nlinarith [norm_nonneg (D+x-e)]
      nlinarith
    · intro hb
      nlinarith [norm_nonneg (D+x-e)]
  change arcA D = circlePt (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) (EA D 0) (EA D 1) (rA D) ''
    Set.Icc (-Real.arccos (cutA D)) (Real.arccos (cutA D))
  rw [circleBandProof _ _ (frameProof D hoff) _ hrr _ (by linarith) hcut1.le]
  change arcA D = {x | x ∈ HardSphereB5.SphericalCrofton.Aux.MovingArc.u D '' Set.Icc (-Real.pi) Real.pi ∧ _}
  rw [movingA_full D hL hoff]
  ext x
  rw [arcA, if_neg hD]
  change (‖x‖=1 ∧ D+x∈LamC) ∧ ‖D+x‖=1 ↔
    (‖x‖=1 ∧ ‖D+x‖=1) ∧ rA D*cutA D ≤ inner ℝ (EA D 0)
      (x-HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)
  constructor
  · rintro ⟨⟨hx,hLx⟩,hDx⟩
    refine ⟨⟨hx,hDx⟩,(hchar x hx hDx).1 ?_⟩
    simpa [LamC, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hLx.2
  · rintro ⟨⟨hx,hDx⟩,hband⟩
    refine ⟨⟨hx,?_,?_⟩,hDx⟩
    · simpa [Metric.mem_closedBall] using hDx.le
    · simpa [Metric.mem_closedBall, dist_eq_norm] using (hchar x hx hDx).2 hband

private theorem cross_add_native (a b c : Pt) : cross a (b+c) = cross a b + cross a c := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring

private theorem cross_smul_native (a b : Pt) (r : ℝ) : cross a (r•b) = r•cross a b := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring

private theorem cross_neg_native (a b : Pt) : cross (-a) (-b) = cross a b := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring

private theorem cross_cross_native (a b : Pt) :
    cross a (cross a b) = (inner ℝ a b)•a - ‖a‖^2•b := by
  ext i; fin_cases i <;>
    simp [SphereGeom.cross, cross_apply, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
      Fin.sum_univ_succ] <;> ring

private theorem cross_center_A (D : Pt) :
    cross (nAv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) = 0 := by
  ext i; fin_cases i <;>
    simp [nAv, HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, SphereGeom.cross, cross_apply] <;> ring

private theorem AderivProof (D : Pt) (hoff : offAxis D) (t : ℝ) :
  HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D)
    (cross (nAv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D t)) t := by
  rcases axisA_facts D hoff with ⟨hD, hn, hr, ho⟩
  have hnf : inner ℝ (nAv D) (EA D 0) = 0 := by
    change inner ℝ (nAv D) (unitDir (rawA D))=0
    rw [unitDir, real_inner_smul_right, ho, mul_zero]
  have hcross1 : cross (nAv D) (EA D 0) = EA D 1 := rfl
  have hcross2 : cross (nAv D) (EA D 1) = -(EA D 0) := by
    change cross (nAv D) (cross (nAv D) (EA D 0))=-(EA D 0)
    rw [cross_cross_native, hnf, hn]
    simp
  have hd : HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D)
      (rA D • ((-Real.sin t)•EA D 0 + Real.cos t•EA D 1)) t := by
    have hc := (Real.hasDerivAt_cos t).smul_const (EA D 0)
    have hs := (Real.hasDerivAt_sin t).smul_const (EA D 1)
    change HasDerivAt (fun z : ℝ => HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D +
      rA D • (Real.cos z • EA D 0 + Real.sin z • EA D 1)) _ t
    exact ((hc.add hs).const_smul (rA D)).const_add (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)
  apply hd.congr_deriv
  simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, circlePt, cross_add_native,
    cross_center_A, cross_smul_native, hcross1, hcross2, zero_add]
  module

private theorem reflect_axis (D : Pt) : nAv (e-D)= -nBv D := by
  simp only [nAv, nBv, norm_sub_rev e D, smul_neg]

private theorem reflect_raw (D : Pt) : rawA (e-D)= -rawB D := by
  rw [rawA, reflect_axis, rawB]
  simp only [inner_neg_left, inner_neg_right, neg_smul, smul_neg]
  module

private theorem reflect_unit (D : Pt) : unitDir (rawA (e-D))= -unitDir (rawB D) := by
  rw [reflect_raw]
  simp [unitDir]

private theorem reflect_E0 (D : Pt) : EA (e-D) 0= -(EB D 0) := by
  simpa only [EA, EB, Matrix.cons_val_zero] using reflect_unit D

private theorem reflect_E1 (D : Pt) : EA (e-D) 1= -(EB D 1) := by
  change cross (nAv (e-D)) (unitDir (rawA (e-D)))=
    -(-cross (nBv D) (unitDir (rawB D)))
  rw [reflect_axis, reflect_unit, cross_neg_native, neg_neg]

private theorem reflect_center (D : Pt) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.cA (e-D)= -HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D := by
  simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.cA, HardSphereB5.SphericalCrofton.Aux.MovingArc.cB]
  module

private theorem reflect_radius (D : Pt) : rA (e-D)=rB D := by
  simp only [rA, rB, norm_sub_rev e D]

private theorem reflect_cut (D : Pt) : cutA (e-D)=cutB D := by
  have he : inner ℝ (e:Pt) e=1 := by simp [real_inner_self_eq_norm_sq, e]
  simp only [cutA, cutB, reflect_radius, reflect_raw, norm_neg, inner_sub_left, he]
  congr 1
  ring

private theorem reflect_half (D : Pt) : halfA (e-D)=halfB D := by
  simp only [halfA, halfB, reflect_cut]

private theorem reflect_chart (D : Pt) (t : ℝ) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) t= -HardSphereB5.SphericalCrofton.Aux.MovingArc.v D t := by
  simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, HardSphereB5.SphericalCrofton.Aux.MovingArc.v,
    circlePt, reflect_center, reflect_E0, reflect_E1, reflect_radius]
  module

private theorem reflect_hypotheses (D : Pt) (hL : D∈LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D-e‖<1) :
    e-D∈LamC ∧ offAxis (e-D) ∧ Rc ‖e-D‖ ‖(e-D)-e‖<1 := by
  have hd : (e-D)-e = -D := by abel
  have hswap (a b : ℝ) : Rc a b=Rc b a := by
    unfold Rc
    have hprod : (a+b+1)*(a+b-1)*(a-b+1)*(-a+b+1)=
        (b+a+1)*(b+a-1)*(b-a+1)*(-b+a+1) := by ring
    rw [hprod, mul_comm a b]
  refine ⟨?_, ?_, ?_⟩
  · have hh : ‖D‖≤1 ∧ ‖D-e‖≤1 := by
      simpa only [LamC, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
        dist_eq_norm, sub_zero] using hL
    simpa only [LamC, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
      dist_eq_norm, sub_zero, hd, norm_neg, norm_sub_rev e D] using And.intro hh.2 hh.1
  · intro t ht
    apply hoff (1-t)
    calc
      D = e-(e-D) := by abel
      _ = e-t•e := by rw [ht]
      _ = (1-t)•e := by module
  · rw [norm_sub_rev e D, hd, norm_neg, hswap]
    exact hR

private theorem reflect_arc_mem (D : Pt) (hoff : offAxis D) (x : Pt) :
    x∈arcB D ↔ -x∈arcA (e-D) := by
  have hde : D≠e := by
    intro h
    exact hoff 1 (by simpa using h)
  have heD : e-D≠0 := sub_ne_zero.mpr (Ne.symm hde)
  have hs : (e-D)+(-x)= -(D+x-e) := by abel
  have ht : -(D+x-e)-e= -(D+x) := by abel
  simp only [arcA, arcB, if_neg hde, if_neg heD, Set.mem_setOf_eq, SigmaD,
    LamC, Set.mem_inter_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero, hs, ht, norm_neg]
  tauto

private theorem BgeometryProof (D : Pt)
  (hL : D ∈ LamC) (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1) :
  Orthonormal ℝ (EB D) ∧ 0 < rB D ∧
  0 < halfB D ∧ halfB D ≤ Real.pi ∧
  arcB D = HardSphereB5.SphericalCrofton.Aux.MovingArc.v D '' Set.Icc (-(halfB D)) (halfB D) ∧
  ∀ t : ℝ, HasDerivAt (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D)
    (-cross (nBv D) (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D t)) t := by
  rcases reflect_hypotheses D hL hoff hR with ⟨hLr,hoffr,hRr⟩
  have hframe := frameProof (e-D) hoffr
  have hhalf : 0<halfB D := by
    rw [← reflect_half, halfA]
    exact Real.arccos_pos.2 (cutBoundsProof (e-D) hLr hoffr hRr).2
  have hrB : 0<rB D := by
    rw [← reflect_radius]
    exact (movingA_radius (e-D) hLr).1
  refine ⟨?_, hrB, hhalf, Real.arccos_le_pi _, ?_, ?_⟩
  · rw [orthonormal_iff_ite] at hframe ⊢
    intro i j
    have hreflect (i : Fin 2) : EA (e-D) i= -(EB D i) := by
      fin_cases i
      · exact reflect_E0 D
      · exact reflect_E1 D
    simpa only [hreflect, inner_neg_left, inner_neg_right, neg_neg] using hframe i j
  · have ha := arcAProof (e-D) hLr hoffr hRr
    rw [reflect_half] at ha
    ext x
    rw [reflect_arc_mem D hoff, ha]
    constructor
    · rintro ⟨t,ht,hx⟩
      refine ⟨t,ht,?_⟩
      rw [reflect_chart] at hx
      exact neg_injective hx
    · rintro ⟨t,ht,hx⟩
      exact ⟨t,ht,by rw [reflect_chart,hx]⟩
  · intro t
    have hd := (AderivProof (e-D) hoffr t).neg
    change HasDerivAt (fun t => -HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) t)
      (-cross (nAv (e-D)) (HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) t)) t at hd
    have hf : (fun t => -HardSphereB5.SphericalCrofton.Aux.MovingArc.u (e-D) t)=
        HardSphereB5.SphericalCrofton.Aux.MovingArc.v D := by
      funext s
      rw [reflect_chart, neg_neg]
    rw [hf, reflect_axis, reflect_chart, cross_neg_native] at hd
    exact hd

private noncomputable def rotateFrame (E : Fin 2→Pt) (h : ℝ) : Fin 2→Pt :=
  ![Real.cos h • E 0 - Real.sin h • E 1,
    Real.sin h • E 0 + Real.cos h • E 1]

private theorem rotateFrame_orthonormal (E : Fin 2→Pt) (he : Orthonormal ℝ E) (h : ℝ) :
    Orthonormal ℝ (rotateFrame E h) := by
  have hinner := orthonormal_iff_ite.mp he
  have h00 : inner ℝ (E 0) (E 0)=1 := by simpa using hinner 0 0
  have h01 : inner ℝ (E 0) (E 1)=0 := by simpa using hinner 0 1
  have h10 : inner ℝ (E 1) (E 0)=0 := by simpa using hinner 1 0
  have h11 : inner ℝ (E 1) (E 1)=1 := by simpa using hinner 1 1
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · change inner ℝ (Real.cos h • E 0 - Real.sin h • E 1) (Real.cos h • E 0 - Real.sin h • E 1) = 1
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, h00,h01,h10,h11]
    nlinarith [Real.sin_sq_add_cos_sq h]
  · change inner ℝ (Real.cos h • E 0 - Real.sin h • E 1) (Real.sin h • E 0 + Real.cos h • E 1) = 0
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, h00,h01,h10,h11]
    nlinarith [Real.sin_sq_add_cos_sq h]
  · change inner ℝ (Real.sin h • E 0 + Real.cos h • E 1) (Real.cos h • E 0 - Real.sin h • E 1) = 0
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, h00,h01,h10,h11]
    nlinarith [Real.sin_sq_add_cos_sq h]
  · change inner ℝ (Real.sin h • E 0 + Real.cos h • E 1) (Real.sin h • E 0 + Real.cos h • E 1) = 1
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, h00,h01,h10,h11]
    nlinarith [Real.sin_sq_add_cos_sq h]

private theorem rotated_circle (c : Pt) (E : Fin 2→Pt) (r h t : ℝ) :
    circlePt c (rotateFrame E h 0) (rotateFrame E h 1) r t=
      circlePt c (E 0) (E 1) r (t-h) := by
  simp only [circlePt, rotateFrame, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.cos_sub, Real.sin_sub]
  module

private theorem shift_interval_image (f : ℝ→Pt) (h : ℝ) :
    f '' Set.Icc (-h) h = (fun t => f (t-h)) '' Set.Icc 0 (2*h) := by
  ext x
  constructor
  · rintro ⟨t,ht,htx⟩
    refine ⟨t+h,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    simpa only [add_sub_cancel_right] using htx
  · rintro ⟨t,ht,htx⟩
    exact ⟨t-h,⟨by linarith [ht.1],by linarith [ht.2]⟩,htx⟩

private theorem shiftedChartWitness (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) :
    ∃ C : HardSphereB5.SphericalCrofton.Aux.Santalo.Charts,
      HardSphereB5.SphericalCrofton.Aux.Santalo.IsChart D C ∧
      HardSphereB5.SphericalCrofton.Aux.Santalo.u D C = (fun t => HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (t-halfA D)) ∧
      HardSphereB5.SphericalCrofton.Aux.Santalo.v D C = (fun t => HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (t-halfB D)) ∧
      C.TA = 2*halfA D ∧ C.TB = 2*halfB D := by
  let C : HardSphereB5.SphericalCrofton.Aux.Santalo.Charts := {
    oA := HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D,
    oB := HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D,
    EA := rotateFrame (EA D) (halfA D),
    EB := rotateFrame (EB D) (halfB D),
    TA := 2*halfA D,
    TB := 2*halfB D }
  have hAframe := frameProof D hoff
  have hAradius := (movingA_radius D hD).1
  have hAhalf : 0<halfA D := by
    rw [halfA]
    exact Real.arccos_pos.2 (cutBoundsProof D hD hoff hR).2
  rcases BgeometryProof D hD hoff hR with ⟨hBframe,hBradius,hBhalf,hBspan,hBimage,hBderiv⟩
  have hAu : HardSphereB5.SphericalCrofton.Aux.Santalo.u D C =
      fun t => HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (t-halfA D) := by
    funext t
    exact rotated_circle (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) (EA D) (rA D) (halfA D) t
  have hBv : HardSphereB5.SphericalCrofton.Aux.Santalo.v D C =
      fun t => HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (t-halfB D) := by
    funext t
    exact rotated_circle (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D) (EB D) (rB D) (halfB D) t
  refine ⟨C, ?_, hAu, hBv, rfl, rfl⟩
  refine ⟨?_,?_,hAradius,hBradius,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact rotateFrame_orthonormal _ hAframe _
  · exact rotateFrame_orthonormal _ hBframe _
  · change 0<2*halfA D
    linarith
  · change 0<2*halfB D
    linarith
  · change 2*halfA D≤2*Real.pi
    exact mul_le_mul_of_nonneg_left (Real.arccos_le_pi _) (by norm_num)
  · change 2*halfB D≤2*Real.pi
    exact mul_le_mul_of_nonneg_left hBspan (by norm_num)
  · change arcA D=HardSphereB5.SphericalCrofton.Aux.Santalo.u D C '' Set.Icc 0 (2*halfA D)
    rw [hAu,← shift_interval_image]
    exact arcAProof D hD hoff hR
  · change arcB D=HardSphereB5.SphericalCrofton.Aux.Santalo.v D C '' Set.Icc 0 (2*halfB D)
    rw [hBv,← shift_interval_image]
    exact hBimage
  · intro t
    rw [hAu]
    have hshift : HasDerivAt (fun s : ℝ => s-halfA D) (1 : ℝ) t :=
      (hasDerivAt_id t).sub_const (halfA D)
    have hc := (AderivProof D hoff (t-halfA D)).scomp t hshift
    simpa only [Function.comp_def, one_smul] using hc
  · intro t
    rw [hBv]
    have hshift : HasDerivAt (fun s : ℝ => s-halfB D) (1 : ℝ) t :=
      (hasDerivAt_id t).sub_const (halfB D)
    have hc := (hBderiv (t-halfB D)).scomp t hshift
    simpa only [Function.comp_def, one_smul] using hc

private theorem cross_smul_left_native (a b : Pt) (r : ℝ) :
    cross (r • a) b = r • cross a b := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring

private theorem cross_sub_left_native (a b c : Pt) :
    cross (a - b) c = cross a c - cross b c := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring

private theorem cross_sub_right_native (a b c : Pt) :
    cross a (b - c) = cross a b - cross a c := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply] <;> ring

private theorem cross_self_native (a : Pt) : cross a a = 0 := by
  ext i; fin_cases i <;> simp [SphereGeom.cross, cross_apply]

private theorem frames_same_normal (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) : EA D 1 = EB D 1 := by
  have hDa : D ≠ 0 := (axisA_facts D hoff).1
  have hDb : D - e ≠ 0 := sub_ne_zero.mpr (by
    intro he
    exact hoff 1 (by simpa using he))
  have hrawA : 0 < ‖rawA D‖ := norm_pos_iff.mpr (axisA_facts D hoff).2.2.1
  have hrawB : 0 < ‖rawB D‖ := by
    have hh := norm_pos_iff.mpr (axisA_facts (e-D) (reflect_hypotheses D hD hoff hR).2.1).2.2.1
    simpa only [reflect_raw, norm_neg] using hh
  let z : Pt := -cross D e
  let l : ℝ := ‖rawA D‖⁻¹ * ‖D‖⁻¹
  let m : ℝ := ‖rawB D‖⁻¹ * ‖D-e‖⁻¹
  have hl : 0 < l := mul_pos (inv_pos.mpr hrawA) (inv_pos.mpr (norm_pos_iff.mpr hDa))
  have hm : 0 < m := mul_pos (inv_pos.mpr hrawB) (inv_pos.mpr (norm_pos_iff.mpr hDb))
  have hA : EA D 1 = l • z := by
    change cross (nAv D) (unitDir (rawA D)) = l • z
    rw [unitDir, cross_smul_native, rawA, cross_sub_right_native,
      cross_smul_native, cross_self_native, smul_zero, sub_zero,
      nAv, cross_smul_left_native]
    change ‖rawA D‖⁻¹ • (‖D‖⁻¹ • cross (-D) e) = l • z
    have hn : cross (-D) e = -cross D e := by
      simpa using cross_smul_left_native D e (-1)
    rw [hn, smul_smul]
  have hB : EB D 1 = m • z := by
    change -cross (nBv D) (unitDir (rawB D)) = m • z
    rw [unitDir, cross_smul_native, rawB, cross_sub_right_native,
      cross_smul_native, cross_self_native, smul_zero, sub_zero,
      nBv, cross_smul_left_native]
    have hn : cross (e-D) (-e) = cross D e := by
      rw [cross_sub_left_native]
      have he0 : cross e (-e) = 0 := by
        simpa only [neg_one_smul, cross_self_native, neg_zero] using cross_smul_native e e (-1)
      have hd0 : cross D (-e) = -cross D e := by
        simpa using cross_smul_native D e (-1)
      rw [he0, hd0]
      simp
    rw [hn]
    simp only [m, z, rawB, nBv, smul_smul, ← smul_neg]
  have hnA := (frameProof D hoff).norm_eq_one (1 : Fin 2)
  have hnB := (BgeometryProof D hD hoff hR).1.norm_eq_one (1 : Fin 2)
  rw [hA, norm_smul, Real.norm_eq_abs, abs_of_pos hl] at hnA
  rw [hB, norm_smul, Real.norm_eq_abs, abs_of_pos hm] at hnB
  have hz : 0 < ‖z‖ := by nlinarith [norm_nonneg z]
  have hlm : l = m := by nlinarith
  rw [hA, hB, hlm]

private theorem normal_center_A (D : Pt) :
    inner ℝ (EA D 1) (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D) = 0 := by
  have ho := cross_inner_first (nAv D) (unitDir (rawA D))
  rw [nAv, real_inner_smul_left, inner_neg_left] at ho
  have hoD : inner ℝ D (cross (nAv D) (unitDir (rawA D))) = 0 := by
    by_cases hz : D = 0
    · simp [hz]
    · exact neg_eq_zero.mp ((mul_eq_zero.mp ho).resolve_left
        (inv_ne_zero (norm_ne_zero_iff.mpr hz)))
  change inner ℝ (cross (nAv D) (unitDir (rawA D))) ((-1/2 : ℝ) • D) = 0
  rw [real_inner_smul_right, real_inner_comm D _, hoD, mul_zero]

private theorem normal_center_B (D : Pt) :
    inner ℝ (EB D 1) (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D) = 0 := by
  have hA := normal_center_A (e-D)
  rw [reflect_E1, reflect_center, inner_neg_left, inner_neg_right, neg_neg] at hA
  exact hA

private theorem reflect_verts_mem (D x : Pt) :
    x ∈ vertsD D ↔ -x ∈ vertsD (e-D) := by
  have hs : (e-D)+(-x) = -(D+x-e) := by abel
  have ht : -(D+x-e)-e = -(D+x) := by abel
  simp only [vertsD, Set.mem_setOf_eq, dist_eq_norm, hs, ht, norm_neg]
  tauto

private theorem endpoint_alignment (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D-e‖ < 1) :
    HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (-halfB D) = HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (-halfA D) ∧
      HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (halfB D) = HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (halfA D) := by
  rcases reflect_hypotheses D hD hoff hR with ⟨hDr, hoffr, hRr⟩
  have hvertsA := HardSphereB5.SphericalCrofton.Aux.MovingArc.endpointsA D hD hoff hR
  have hvertsB := HardSphereB5.SphericalCrofton.Aux.MovingArc.endpointsA (e-D) hDr hoffr hRr
  have hBmem (t : ℝ) (ht : t = -halfB D ∨ t = halfB D) :
      HardSphereB5.SphericalCrofton.Aux.MovingArc.v D t ∈ vertsD D := by
    rw [reflect_verts_mem, hvertsB, reflect_half]
    rw [reflect_chart, reflect_chart]
    rcases ht with rfl | rfl <;> simp
  have hsinA : 0 < Real.sin (halfA D) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact Real.arccos_pos.mpr (cutBoundsProof D hD hoff hR).2
    · exact Real.arccos_lt_pi.mpr (by linarith [(cutBoundsProof D hD hoff hR).1])
  have hsinB : 0 < Real.sin (halfB D) := by
    rw [← reflect_half]
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact Real.arccos_pos.mpr (cutBoundsProof (e-D) hDr hoffr hRr).2
    · exact Real.arccos_lt_pi.mpr (by linarith [(cutBoundsProof (e-D) hDr hoffr hRr).1])
  have hrA := (movingA_radius D hD).1
  have hrB := (BgeometryProof D hD hoff hR).2.1
  have hsame := frames_same_normal D hD hoff hR
  have hcoordA (t : ℝ) :
      inner ℝ (EA D 1) (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D t) = rA D * Real.sin t := by
    have hf := orthonormal_iff_ite.mp (frameProof D hoff)
    simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.u, circlePt, inner_add_right,
      real_inner_smul_right, normal_center_A]
    simp only [hf, Fin.isValue, one_ne_zero, ite_false, ite_true, mul_zero, mul_one, zero_add]
  have hcoordB (t : ℝ) :
      inner ℝ (EA D 1) (HardSphereB5.SphericalCrofton.Aux.MovingArc.v D t) = rB D * Real.sin t := by
    rw [hsame]
    have hf := orthonormal_iff_ite.mp (BgeometryProof D hD hoff hR).1
    simp only [HardSphereB5.SphericalCrofton.Aux.MovingArc.v, circlePt, inner_add_right,
      real_inner_smul_right, normal_center_B]
    simp only [hf, Fin.isValue, one_ne_zero, ite_false, ite_true, mul_zero, mul_one, zero_add]
  constructor
  · have hm := hBmem (-halfB D) (Or.inl rfl)
    rw [hvertsA, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with hm | hm
    · exact hm
    · have hh := congrArg (inner ℝ (EA D 1)) hm
      rw [hcoordA, hcoordB, Real.sin_neg] at hh
      nlinarith [mul_pos hrA hsinA, mul_pos hrB hsinB]
  · have hm := hBmem (halfB D) (Or.inr rfl)
    rw [hvertsA, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with hm | hm
    · have hh := congrArg (inner ℝ (EA D 1)) hm
      rw [hcoordA, hcoordB, Real.sin_neg] at hh
      nlinarith [mul_pos hrA hsinA, mul_pos hrB hsinB]
    · exact hm

private theorem endpoint_inner_Rc (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D-e‖ < 1) :
    inner ℝ (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (-halfA D))
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (halfA D)) =
        2 * Rc ‖D‖ ‖D-e‖ ^ 2 - 1 := by
  let x : Pt := nAv D
  let y : Pt := nBv D
  let a : ℝ := ‖D‖ / 2
  let b : ℝ := ‖D-e‖ / 2
  let c : ℝ := inner ℝ x y
  let k : ℝ := 1-c^2
  obtain ⟨hx, hy, hk, ha, hb, hla, hlb, hRC, hRC0, hSigma, hverts⟩ :=
    HardSphereB5.SphericalCrofton.Aux.Geom.sigma_gram_data D hD hoff
  change ‖x‖ = 1 at hx
  change ‖y‖ = 1 at hy
  change 0 < k at hk
  change (a^2-2*c*a*b+b^2)/k = Rc ‖D‖ ‖D-e‖ ^ 2 at hRC
  let U : Pt := HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (-halfA D)
  let V : Pt := HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (halfA D)
  let q : Pt := (1/2 : ℝ) • (U+V)
  have hpair := HardSphereB5.SphericalCrofton.Aux.MovingArc.endpointsA D hD hoff hR
  have hU : U ∈ vertsD D := by rw [hpair]; simp [U]
  have hV : V ∈ vertsD D := by rw [hpair]; simp [V]
  rw [hverts] at hU hV
  change ‖U‖ = 1 ∧ inner ℝ x U = a ∧ inner ℝ y U = b at hU
  change ‖V‖ = 1 ∧ inner ℝ x V = a ∧ inner ℝ y V = b at hV
  have hqx : inner ℝ x q = a := by
    dsimp only [q]
    rw [real_inner_smul_right, inner_add_right, hU.2.1, hV.2.1]
    ring
  have hqy : inner ℝ y q = b := by
    dsimp only [q]
    rw [real_inner_smul_right, inner_add_right, hU.2.2, hV.2.2]
    ring
  have hqexp : q = HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D +
      (rA D * Real.cos (halfA D)) • EA D 0 := by
    dsimp only [q, U, V, HardSphereB5.SphericalCrofton.Aux.MovingArc.u, circlePt]
    rw [Real.cos_neg, Real.sin_neg]
    module
  have hD0 : D ≠ 0 := (axisA_facts D hoff).1
  have hDe0 : D-e ≠ 0 := sub_ne_zero.mpr (by
    intro he
    exact hoff 1 (by simpa using he))
  have hDx : D = (-‖D‖) • x := by
    simp [x, nAv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hD0)]
  have hey : e = D + ‖D-e‖ • y := by
    simp [y, nBv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hDe0)]
  let s : ℝ := rA D * Real.cos (halfA D) * ‖rawA D‖⁻¹
  let L : ℝ := a - s * (‖D‖ + inner ℝ x e)
  let M : ℝ := s * ‖D-e‖
  have hcenter : HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D = a • x := by
    change (-1/2 : ℝ) • D = a • x
    calc
      _ = (-1/2 : ℝ) • ((-‖D‖) • x) := congrArg (fun w : Pt => (-1/2 : ℝ) • w) hDx
      _ = a • x := by dsimp only [a]; module
  have hrawlinear : rawA D = ((-‖D‖)-inner ℝ x e) • x + ‖D-e‖ • y := by
    change e - (inner ℝ x e) • x = _
    calc
      _ = (D + ‖D-e‖ • y) - (inner ℝ x e) • x :=
        congrArg (fun w : Pt => w - (inner ℝ x e) • x) hey
      _ = ((-‖D‖) • x + ‖D-e‖ • y) - (inner ℝ x e) • x :=
        congrArg (fun w : Pt => w + ‖D-e‖ • y - (inner ℝ x e) • x) hDx
      _ = _ := by module
  have hqlinear : q = L • x + M • y := by
    calc
      q = a • x + s • rawA D := by
        rw [hqexp, hcenter]
        simp only [EA, Matrix.cons_val_zero, unitDir, smul_smul, s]
      _ = a • x + s • (((-‖D‖)-inner ℝ x e) • x + ‖D-e‖ • y) :=
        congrArg (fun w : Pt => a • x + s • w) hrawlinear
      _ = L • x + M • y := by dsimp only [L, M]; module
  have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyy : inner ℝ y y = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hxy : inner ℝ x y = c := rfl
  have hyx : inner ℝ y x = c := real_inner_comm x y
  have hLcond : L+c*M = a := by
    rw [hqlinear, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, hxx, hxy] at hqx
    nlinarith only [hqx]
  have hMcond : c*L+M = b := by
    rw [hqlinear, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, hyx, hyy] at hqy
    nlinarith only [hqy]
  have hL : L = (a-c*b)/k := by
    apply (eq_div_iff (ne_of_gt hk)).mpr
    dsimp only [k]
    linear_combination hLcond - c * hMcond
  have hM : M = (b-c*a)/k := by
    apply (eq_div_iff (ne_of_gt hk)).mpr
    dsimp only [k]
    linear_combination hMcond - c * hLcond
  obtain ⟨hpX, hpY, hpN⟩ :=
    HardSphereB5.SphericalCrofton.Aux.Geom.gram_projection x y a b c hx hy rfl hk
  change ‖((a-c*b)/k) • x + ((b-c*a)/k) • y‖ ^ 2 =
    (a^2-2*c*a*b+b^2)/k at hpN
  have hqN : ‖q‖^2 = Rc ‖D‖ ‖D-e‖ ^ 2 := by
    rw [hqlinear, hL, hM]
    exact hpN.trans hRC
  have hqsum : 4*‖q‖^2 = ‖U+V‖^2 := by
    dsimp only [q]
    rw [norm_smul]
    norm_num [Real.norm_eq_abs, mul_pow]
    ring
  have hsum := norm_add_sq_real U V
  have hsub := norm_sub_sq_real U V
  rw [hU.1, hV.1] at hsum hsub
  have hwidth := HardSphereB5.SphericalCrofton.Aux.MovingArc.endpointsA_width D hD hoff hR
  have hdist : ‖U-V‖ = 2*rA D*Real.sin (halfA D) := by
    simpa only [dist_eq_norm, U, V] using hwidth
  have hdistSq := congrArg (fun z : ℝ => z^2) hdist
  have hchord : (2*rA D*Real.sin (halfA D))^2 =
      4*(1-Rc ‖D‖ ‖D-e‖^2) := by
    nlinarith only [hqN, hqsum, hsum, hsub, hdistSq]
  change inner ℝ U V = 2*Rc ‖D‖ ‖D-e‖^2-1
  nlinarith only [hsub, hdistSq, hchord]

open HardSphereB5.SphericalCrofton.Aux.Santalo (Charts IsChart delta)

private theorem cornerWitnessExtras (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D-e‖ < 1) :
    ∃ C : Charts, IsChart D C ∧
      HardSphereB5.SphericalCrofton.Aux.Santalo.u D C = (fun t => HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (t-halfA D)) ∧
      HardSphereB5.SphericalCrofton.Aux.Santalo.v D C = (fun t => HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (t-halfB D)) ∧
      C.TA = 2*halfA D ∧ C.TB = 2*halfB D ∧ delta D C C.TA C.TB = 0 ∧
      delta D C C.TA 0 = deltaV D ∧ delta D C 0 C.TB = deltaV D ∧
      delta D C 0 0 = 0 := by
  rcases shiftedChartWitness D hD hoff hR with ⟨C, hC, hAu, hBv, hTA, hTB⟩
  rcases endpoint_alignment D hD hoff hR with ⟨hminus, hplus⟩
  have hinner := endpoint_inner_Rc D hD hoff hR
  have hverts := HardSphereB5.SphericalCrofton.Aux.MovingArc.endpointsA D hD hoff hR
  have hU : HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (-halfA D) ∈ vertsD D := by
    rw [hverts]; simp
  have hV : HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (halfA D) ∈ vertsD D := by
    rw [hverts]; simp
  have hnU : ‖HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (-halfA D)‖ = 1 := hU.1
  have hnV : ‖HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (halfA D)‖ = 1 := hV.1
  have hsA : 2*halfA D-halfA D = halfA D := by ring
  have hsB : 2*halfB D-halfB D = halfB D := by ring
  refine ⟨C,hC,hAu,hBv,hTA,hTB,?_,?_,?_,?_⟩
  · simp only [delta, hAu, hBv, hTA, hTB, hsA, hsB, hplus,
      real_inner_self_eq_norm_sq, hnV, one_pow, Real.arccos_one]
  · simp only [delta, hAu, hBv, hTA, hsA, zero_sub, hminus]
    rw [real_inner_comm (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (-halfA D))
      (HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (halfA D)), hinner]
    rfl
  · simp only [delta, hAu, hBv, hTB, hsB, zero_sub, hplus, hinner]
    rfl
  · simp only [delta, hAu, hBv, zero_sub, hminus,
      real_inner_self_eq_norm_sq, hnU, one_pow, Real.arccos_one]

private theorem small_circle_inj (c : Pt) (E : Fin 2 → Pt) (r h : ℝ)
    (hE : Orthonormal ℝ E) (hr : 0 < r) (hh : h ≤ Real.pi/2) :
    Set.InjOn (circlePt c (E 0) (E 1) r) (Set.Icc (-h) h) := by
  have hcoord (z : ℝ) : inner ℝ (E 1) (circlePt c (E 0) (E 1) r z-c) =
      r*Real.sin z := by
    simp [circlePt,inner_add_right,real_inner_smul_right,
      orthonormal_iff_ite.mp hE,hE.norm_eq_one]
  intro p hp q hq heq
  have he := congrArg (fun z : Pt => inner ℝ (E 1) (z-c)) heq
  rw [hcoord,hcoord] at he
  have hsin : Real.sin p = Real.sin q := (mul_left_cancel₀ (ne_of_gt hr)) he
  exact Real.injOn_sin
    (show p ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hp.1],by linarith [hp.2]⟩)
    (show q ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [hq.1],by linarith [hq.2]⟩) hsin

private theorem canonical_closed_range (D : Pt) (hD : D ∈ LamC)
    (hoff : offAxis D) (hR : Rc ‖D‖ ‖D-e‖ < 1) (C : Charts) (hC : IsChart D C)
    (hAu : HardSphereB5.SphericalCrofton.Aux.Santalo.u D C =
      (fun t => HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (t-halfA D)))
    (hBv : HardSphereB5.SphericalCrofton.Aux.Santalo.v D C =
      (fun t => HardSphereB5.SphericalCrofton.Aux.MovingArc.v D (t-halfB D)))
    (hTA : C.TA = 2*halfA D) (hTB : C.TB = 2*halfB D) :
    ∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB,
      ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) →
        inner ℝ (HardSphereB5.SphericalCrofton.Aux.Santalo.u D C t)
          (HardSphereB5.SphericalCrofton.Aux.Santalo.v D C s) ∈ Set.Ioo (-1) 1 := by
  have hhalfA : halfA D ≤ Real.pi/2 := by
    have hc := cutBoundsProof D hD hoff hR
    have he := Real.arccos_lt_arccos (by norm_num : (-1:ℝ) ≤ 0) hc.1 hc.2.le
    have hlt : halfA D < Real.pi/2 := by simpa only [Real.arccos_zero,halfA] using he
    exact hlt.le
  have hhalfB : halfB D ≤ Real.pi/2 := by
    rcases reflect_hypotheses D hD hoff hR with ⟨hDr,hoffr,hRr⟩
    have hc := cutBoundsProof (e-D) hDr hoffr hRr
    have he := Real.arccos_lt_arccos (by norm_num : (-1:ℝ) ≤ 0) hc.1 hc.2.le
    rw [← reflect_half]
    have hlt : halfA (e-D) < Real.pi/2 := by simpa only [Real.arccos_zero,halfA] using he
    exact hlt.le
  have hrawInjA := small_circle_inj (HardSphereB5.SphericalCrofton.Aux.MovingArc.cA D)
    (EA D) (rA D) (halfA D) (frameProof D hoff) (movingA_radius D hD).1 hhalfA
  have hrawInjB := small_circle_inj (HardSphereB5.SphericalCrofton.Aux.MovingArc.cB D)
    (EB D) (rB D) (halfB D) (BgeometryProof D hD hoff hR).1
    (BgeometryProof D hD hoff hR).2.1 hhalfB
  have hInjA : Set.InjOn (HardSphereB5.SphericalCrofton.Aux.Santalo.u D C) (Set.Icc 0 C.TA) := by
    intro p hp q hq heq
    rw [hAu] at heq
    rw [hTA] at hp hq
    have hh := hrawInjA
      (show p-halfA D ∈ Set.Icc (-halfA D) (halfA D) from
        ⟨by linarith [hp.1],by linarith [hp.2]⟩)
      (show q-halfA D ∈ Set.Icc (-halfA D) (halfA D) from
        ⟨by linarith [hq.1],by linarith [hq.2]⟩) heq
    linarith
  have hInjB : Set.InjOn (HardSphereB5.SphericalCrofton.Aux.Santalo.v D C) (Set.Icc 0 C.TB) := by
    intro p hp q hq heq
    rw [hBv] at heq
    rw [hTB] at hp hq
    have hh := hrawInjB
      (show p-halfB D ∈ Set.Icc (-halfB D) (halfB D) from
        ⟨by linarith [hp.1],by linarith [hp.2]⟩)
      (show q-halfB D ∈ Set.Icc (-halfB D) (halfB D) from
        ⟨by linarith [hq.1],by linarith [hq.2]⟩) heq
    linarith
  rcases endpoint_alignment D hD hoff hR with ⟨hminus,hplus⟩
  have hA0 : HardSphereB5.SphericalCrofton.Aux.Santalo.u D C 0 =
      HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (-halfA D) := by simp only [hAu,zero_sub]
  have hA1 : HardSphereB5.SphericalCrofton.Aux.Santalo.u D C C.TA =
      HardSphereB5.SphericalCrofton.Aux.MovingArc.u D (halfA D) := by
    simp only [hAu,hTA,show 2*halfA D-halfA D=halfA D by ring]
  have hzero : HardSphereB5.SphericalCrofton.Aux.Santalo.u D C 0 =
      HardSphereB5.SphericalCrofton.Aux.Santalo.v D C 0 := by simp only [hAu,hBv,zero_sub,hminus]
  have hone : HardSphereB5.SphericalCrofton.Aux.Santalo.u D C C.TA =
      HardSphereB5.SphericalCrofton.Aux.Santalo.v D C C.TB := by
    simp only [hAu,hBv,hTA,hTB,show 2*halfA D-halfA D=halfA D by ring,
      show 2*halfB D-halfB D=halfB D by ring,hplus]
  intro t ht s hs hnc
  let U := HardSphereB5.SphericalCrofton.Aux.Santalo.u D C t
  let V := HardSphereB5.SphericalCrofton.Aux.Santalo.v D C s
  have hD0 : D ≠ 0 := by simpa using hoff 0
  have hDe : D ≠ e := by simpa using hoff 1
  rcases hC with ⟨_,_,_,_,hTA0,hTB0,_,_,hA,hB,_,_⟩
  have hUm : U ∈ arcA D := by rw [hA]; exact ⟨t,ht,rfl⟩
  have hVm : V ∈ arcB D := by rw [hB]; exact ⟨s,hs,rfl⟩
  simp only [arcA,if_neg hD0,Set.mem_setOf_eq] at hUm
  simp only [arcB,if_neg hDe,Set.mem_setOf_eq] at hVm
  obtain ⟨hnA,hnB,hg,ha,hb,hla,hlb,hRnorm,hRn,hSigma,hVerts⟩ :=
    HardSphereB5.SphericalCrofton.Aux.Geom.sigma_gram_data D hD hoff
  have hUc := hUm.1
  have hVc := hVm.1
  rw [hSigma] at hUc hVc
  have hnU : ‖U‖ = 1 := hUc.1
  have hnV : ‖V‖ = 1 := hVc.1
  have hne : U ≠ V := by
    intro heq
    have hVertex : U ∈ vertsD D := ⟨hnU,hUm.2,by simpa only [heq] using hVm.2⟩
    rw [HardSphereB5.SphericalCrofton.Aux.MovingArc.endpointsA D hD hoff hR,
      Set.mem_insert_iff,Set.mem_singleton_iff,← hA0,← hA1] at hVertex
    rcases hVertex with hVertex | hVertex
    · have ht0 : t=0 := hInjA ht ⟨le_rfl,hTA0.le⟩ hVertex
      have hs0 : s=0 := hInjB hs ⟨le_rfl,hTB0.le⟩
        (heq.symm.trans (hVertex.trans hzero))
      exact hnc (Or.inl ⟨ht0,hs0⟩)
    · have ht1 : t=C.TA := hInjA ht ⟨hTA0.le,le_rfl⟩ hVertex
      have hs1 : s=C.TB := hInjB hs ⟨hTB0.le,le_rfl⟩
        (heq.symm.trans (hVertex.trans hone))
      exact hnc (Or.inr ⟨ht1,hs1⟩)
  have hneadd : U+V ≠ 0 := by
    intro hadd
    have heq : U = -V := eq_neg_of_add_eq_zero_left hadd
    have hAU := hUc.2.1
    have hAV := hVc.2.1
    rw [heq,inner_neg_right] at hAU
    linarith
  have hposAdd : 0 < ‖U+V‖ := norm_pos_iff.mpr hneadd
  have hposSub : 0 < ‖U-V‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hAdd := norm_add_sq_real U V
  have hSub := norm_sub_sq_real U V
  rw [hnU,hnV] at hAdd hSub
  change -1 < inner ℝ U V ∧ inner ℝ U V < 1
  constructor
  · nlinarith [sq_pos_of_pos hposAdd]
  · nlinarith [sq_pos_of_pos hposSub]

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_canonical_closed_density_chain_rule (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D-e‖ < 1) :
    ∃ C : Charts, IsChart D C ∧ delta D C C.TA C.TB = 0 ∧
      delta D C C.TA 0 = deltaV D ∧ delta D C 0 C.TB = deltaV D ∧ delta D C 0 0 = 0 ∧
      (∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB,
        ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) →
          inner ℝ (HardSphereB5.SphericalCrofton.Aux.Santalo.u D C t)
            (HardSphereB5.SphericalCrofton.Aux.Santalo.v D C s) ∈ Set.Ioo (-1) 1) ∧
      (∀ f : Kern, ∀ t ∈ Set.Icc 0 C.TA, ∀ s ∈ Set.Icc 0 C.TB,
        ¬ ((t=0 ∧ s=0) ∨ (t=C.TA ∧ s=C.TB)) →
          HardSphereB5.SphericalCrofton.Aux.Santalo.J f D C t s =
            -HardSphereB5.SphericalCrofton.Aux.Santalo.Q12 f D C t s + HardSphereB5.SphericalCrofton.Aux.Santalo.H f D C t s) := by
  rcases cornerWitnessExtras D hD hoff hR with
    ⟨C,hC,hAu,hBv,hTA,hTB,h11,h10,h01,h00⟩
  have hRange := canonical_closed_range D hD hoff hR C hC hAu hBv hTA hTB
  refine ⟨C,hC,h11,h10,h01,h00,hRange,?_⟩
  intro f t ht s hs hnc
  exact HardSphereB5.SphericalCrofton.Aux.Santalo.density_chain_rule_at f D C hD hoff hR hC t s
    ht hs (hRange t ht s hs hnc)
