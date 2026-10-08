import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
set_option autoImplicit false
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

theorem proof_HardSphereB5_SphericalCrofton_Aux_MovingArc_isChart_exists (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1) :
    ∃ C : HardSphereB5.SphericalCrofton.Aux.Santalo.Charts,
      HardSphereB5.SphericalCrofton.Aux.Santalo.IsChart D C := by
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
  refine ⟨C,?_,?_,hAradius,hBradius,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
