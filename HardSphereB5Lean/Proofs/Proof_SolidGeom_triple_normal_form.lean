import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
open MeasureTheory Real SphereGeom
set_option maxHeartbeats 1200000

private theorem f6_circumcircle_data (c : Fin 3 → SphereGeom.E3)
    (hQ : 0 < 4 * dist (c 0) (c 1)^2 * dist (c 0) (c 2)^2 -
      (dist (c 0) (c 1)^2 + dist (c 0) (c 2)^2 - dist (c 1) (c 2)^2)^2 -
      dist (c 0) (c 1)^2 * dist (c 0) (c 2)^2 * dist (c 1) (c 2)^2) :
    ∃ (o : SphereGeom.E3) (R : ℝ), 0 < R ∧ R < 1 ∧
      (∀ i, ‖o - c i‖ = R) ∧
      (∀ i, o - c i ∈ Submodule.span ℝ {c 1 - c 0, c 2 - c 0}) ∧
      LinearIndependent ℝ ![c 1 - c 0, c 2 - c 0] := by
  let v := c 1 - c 0
  let w := c 2 - c 0
  let a : ℝ := ‖v‖ ^ 2
  let b : ℝ := ‖w‖ ^ 2
  let d : ℝ := inner ℝ v w
  let t : ℝ := ‖v - w‖ ^ 2
  let g : ℝ := a * b - d ^ 2
  have haa : inner ℝ v v = a := real_inner_self_eq_norm_sq v
  have hbb : inner ℝ w w = b := real_inner_self_eq_norm_sq w
  have hd : inner ℝ w v = d := (real_inner_comm w v).symm
  have ht : t = a - 2 * d + b := norm_sub_sq_real v w
  have h01 : dist (c 0) (c 1) ^ 2 = a := by
    dsimp [a, v]
    rw [dist_comm, dist_eq_norm]
  have h02 : dist (c 0) (c 2) ^ 2 = b := by
    dsimp [b, w]
    rw [dist_comm, dist_eq_norm]
  have h12 : dist (c 1) (c 2) ^ 2 = t := by
    dsimp [t]
    rw [dist_eq_norm]
    congr 2
    dsimp [v, w]
    abel
  rw [h01, h02, h12] at hQ
  have habt : a + b - t = 2 * d := by linarith [ht]
  rw [habt] at hQ
  have hq : 0 < 4 * g - a * b * t := by dsimp [g]; nlinarith [hQ]
  have ha0 : 0 ≤ a := sq_nonneg _
  have hb0 : 0 ≤ b := sq_nonneg _
  have ht0 : 0 ≤ t := sq_nonneg _
  have hp : 0 ≤ a * b * t := mul_nonneg (mul_nonneg ha0 hb0) ht0
  have hg : 0 < g := by linarith [hq, hp]
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hab : 0 < a * b := by dsimp [g] at hg; nlinarith [sq_nonneg d]
  have ha : 0 < a := (mul_pos_iff.mp hab).elim (fun h => h.1)
    (fun h => False.elim (not_lt_of_ge ha0 h.1))
  have hb : 0 < b := (mul_pos_iff.mp hab).elim (fun h => h.2)
    (fun h => False.elim (not_lt_of_ge hb0 h.2))
  let α : ℝ := b * (a - d) / (2 * g)
  let η : ℝ := a * (b - d) / (2 * g)
  let u : SphereGeom.E3 := α • v + η • w
  have huv : inner ℝ u v = a / 2 := by
    dsimp [u]
    simp only [inner_add_left, real_inner_smul_left, haa, hd]
    dsimp only [α, η]
    field_simp [hg0]
    <;> (try dsimp only [g])
    <;> ring
  have huw : inner ℝ u w = b / 2 := by
    dsimp [u]
    simp only [inner_add_left, real_inner_smul_left, hbb]
    change α * d + η * b = b / 2
    dsimp only [α, η]
    field_simp [hg0]
    <;> (try dsimp only [g])
    <;> ring
  have huN : ‖u‖ ^ 2 = α * (a / 2) + η * (b / 2) := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => arg 2; dsimp [u]
    rw [inner_add_right, inner_smul_right, inner_smul_right, huv, huw]
  have huFormula : 4 * g * ‖u‖ ^ 2 = a * b * t := by
    rw [huN, ht]
    dsimp only [α, η]
    field_simp [hg0]
    <;> (try dsimp only [g])
    <;> ring
  have hu0 : u ≠ 0 := by
    intro hu
    rw [hu, inner_zero_left] at huv
    linarith
  have hR0 : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hRsq : ‖u‖ ^ 2 < 1 := by
    by_contra h
    have hh : g ≤ g * ‖u‖ ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left (le_of_not_gt h) hg.le
    nlinarith [hq, huFormula]
  have hR1 : ‖u‖ < 1 := by nlinarith [norm_nonneg u]
  have hNv : ‖u - v‖ = ‖u‖ := by
    have hh := norm_sub_sq_real u v
    rw [huv] at hh
    change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * (a / 2) + a at hh
    nlinarith [norm_nonneg (u - v), norm_nonneg u]
  have hNw : ‖u - w‖ = ‖u‖ := by
    have hh := norm_sub_sq_real u w
    rw [huw] at hh
    change ‖u - w‖ ^ 2 = ‖u‖ ^ 2 - 2 * (b / 2) + b at hh
    nlinarith [norm_nonneg (u - w), norm_nonneg u]
  have hLI : LinearIndependent ℝ ![v, w] := by
    apply linearIndependent_fin2.mpr
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    constructor
    · intro hw
      have hh : b = 0 := by simp [b, hw]
      linarith
    · intro r hr
      have ha' : a = r * d := by
        calc
          a = inner ℝ v v := haa.symm
          _ = inner ℝ (r • w) v := congrArg (fun z => inner ℝ z v) hr.symm
          _ = r * d := by rw [real_inner_smul_left, hd]
      have hd' : d = r * b := by
        change inner ℝ v w = r * b
        rw [← hr, real_inner_smul_left, hbb]
      have hz : g = 0 := by dsimp [g]; rw [ha', hd']; ring
      linarith
  let S := Submodule.span ℝ ({v, w} : Set SphereGeom.E3)
  have hvS : v ∈ S := Submodule.subset_span (by simp)
  have hwS : w ∈ S := Submodule.subset_span (by simp)
  have huS : u ∈ S := S.add_mem (S.smul_mem α hvS) (S.smul_mem η hwS)
  have ho0 : c 0 + u - c 0 = u := by abel
  have ho1 : c 0 + u - c 1 = u - v := by dsimp [v]; abel
  have ho2 : c 0 + u - c 2 = u - w := by dsimp [w]; abel
  refine ⟨c 0 + u, ‖u‖, hR0, hR1, ?_, ?_, hLI⟩
  · intro i
    fin_cases i
    · change ‖c 0 + u - c 0‖ = ‖u‖
      rw [ho0]
    · change ‖c 0 + u - c 1‖ = ‖u‖
      rw [ho1, hNv]
    · change ‖c 0 + u - c 2‖ = ‖u‖
      rw [ho2, hNw]
  · intro i
    change c 0 + u - c i ∈ S
    fin_cases i
    · change c 0 + u - c 0 ∈ S
      rw [ho0]; exact huS
    · change c 0 + u - c 1 ∈ S
      rw [ho1]; exact S.sub_mem huS hvS
    · change c 0 + u - c 2 ∈ S
      rw [ho2]; exact S.sub_mem huS hwS

open MeasureTheory Real SphereGeom InnerProductSpace

private theorem f6_circle_coordinates (c : Fin 3 → E3) (o u v : E3) (R : ℝ) (hR : 0 < R)
    (hc : Function.Injective c) (hn : ∀ i, ‖o - c i‖ = R)
    (hp : ∀ i, o - c i ∈ Submodule.span ℝ {u,v}) :
    ∃ (e : Fin 3 → E3) (z : Fin 3 → ℂ), Orthonormal ℝ e ∧
      (∀ i, ‖z i‖ = 1) ∧ Function.Injective z ∧
      ∀ i, o - c i = R • ((z i).re • e 0 + (z i).im • e 1) := by
  classical
  let f : Fin 3 → E3 := ![u,v,0]
  let b : OrthonormalBasis (Fin 3) ℝ E3 :=
    gramSchmidtOrthonormalBasis (by simp [E3]) f
  have hu : b.repr u 2 = 0 := by
    exact gramSchmidtOrthonormalBasis_inv_triangular' (by simp [E3]) f (by decide : (0 : Fin 3) < 2)
  have hv : b.repr v 2 = 0 := by
    exact gramSchmidtOrthonormalBasis_inv_triangular' (by simp [E3]) f (by decide : (1 : Fin 3) < 2)
  have hz' (x : E3) (hx : x ∈ Submodule.span ℝ {u,v}) : b.repr x 2 = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hu
      · have : x = v := Set.mem_singleton_iff.mp hx
        subst x
        exact hv
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul a x _ hx => simp [map_smul, hx]
  have hz (i : Fin 3) : b.repr (o - c i) 2 = 0 := hz' _ (hp i)
  let z : Fin 3 → ℂ := fun i => ⟨b.repr (o-c i) 0 / R, b.repr (o-c i) 1 / R⟩
  have hexp (i : Fin 3) : o - c i = R • ((z i).re • b 0 + (z i).im • b 1) := by
    have hr : R ≠ 0 := ne_of_gt hR
    have hsum := b.sum_repr (o - c i)
    simp only [Fin.sum_univ_three, hz, zero_smul, add_zero] at hsum
    rw [smul_add, smul_smul, smul_smul]
    simp only [z, Complex.re, Complex.im, mul_div_cancel₀ _ hr]
    exact hsum.symm
  refine ⟨b,z,b.orthonormal,?_,?_,hexp⟩
  · intro i
    have hnorm : ‖b.repr (o - c i)‖ = R := by simpa using (b.repr.norm_map (o-c i)).trans (hn i)
    have hsq : (b.repr (o-c i) 0)^2 + (b.repr (o-c i) 1)^2 = R^2 := by
      have hh := congrArg (fun t : ℝ => t^2) hnorm
      simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs,
        sq_abs, hz i, zero_pow (by decide : 2 ≠ 0), add_zero] using hh
    have hzs : ‖z i‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      dsimp [z]
      field_simp
      nlinarith
    have := norm_nonneg (z i)
    nlinarith
  · intro i j hij
    apply hc
    have hvec : o - c i = o - c j := by rw [hexp i, hexp j, hij]
    exact sub_right_injective hvec

private theorem f6_ordered_angles (z₁ z₂ : ℂ) (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1)
    (hn₁ : z₁ ≠ 1) (hn₂ : z₂ ≠ 1) (hne : z₁ ≠ z₂) :
    ∃ (s t₁ t₂ : ℝ), (s = 1 ∨ s = -1) ∧ 0 < t₁ ∧ t₁ < t₂ ∧
      t₂ < 2 * Real.pi ∧ Real.cos t₁ = z₁.re ∧ Real.sin t₁ = s * z₁.im ∧
      Real.cos t₂ = z₂.re ∧ Real.sin t₂ = s * z₂.im := by
  have angle : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 →
      ∃ t : ℝ, 0 < t ∧ t < 2 * Real.pi ∧ Real.cos t = z.re ∧ Real.sin t = z.im := by
    intro z hz hn
    have hc : Real.cos z.arg = z.re := by
      simpa [hz] using Complex.norm_mul_cos_arg z
    have hs : Real.sin z.arg = z.im := by
      simpa [hz] using Complex.norm_mul_sin_arg z
    have ha : z.arg ≠ 0 := by
      intro ha
      apply hn
      apply Complex.ext
      · simpa [ha] using hc.symm
      · simpa [ha] using hs.symm
    by_cases hp : 0 < z.arg
    · refine ⟨z.arg, hp, ?_, hc, hs⟩
      have := Complex.arg_le_pi z
      linarith [Real.pi_pos]
    · have hm : z.arg < 0 := lt_of_le_of_ne (le_of_not_gt hp) ha
      refine ⟨z.arg + 2 * Real.pi, ?_, ?_, ?_, ?_⟩
      · linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
      · linarith
      · simpa [Real.cos_add, Real.sin_add, two_mul] using hc
      · simpa [Real.cos_add, Real.sin_add, two_mul] using hs
  obtain ⟨a, ha0, hap, hac, has⟩ := angle z₁ h₁ hn₁
  obtain ⟨b, hb0, hbp, hbc, hbs⟩ := angle z₂ h₂ hn₂
  have hab : a ≠ b := by
    intro he
    apply hne
    apply Complex.ext
    · rw [← hac, ← hbc, he]
    · rw [← has, ← hbs, he]
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact ⟨1, a, b, Or.inl rfl, ha0, hab, hbp, hac, by simpa using has,
      hbc, by simpa using hbs⟩
  · refine ⟨-1, 2 * Real.pi - a, 2 * Real.pi - b, Or.inr rfl,
      by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_⟩
    · simpa [Real.cos_sub, Real.cos_add, Real.sin_add, two_mul] using hac
    · simpa [Real.sin_sub, Real.cos_add, Real.sin_add, two_mul] using congrArg Neg.neg has
    · simpa [Real.cos_sub, Real.cos_add, Real.sin_add, two_mul] using hbc
    · simpa [Real.sin_sub, Real.cos_add, Real.sin_add, two_mul] using congrArg Neg.neg hbs

private theorem f6_three_angles (z : Fin 3 → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective z) :
    ∃ (s ψ t₁ t₂ : ℝ), (s = 1 ∨ s = -1) ∧ 0 < t₁ ∧ t₁ < t₂ ∧
      t₂ < 2 * Real.pi ∧ Real.cos ψ = (z 0).re ∧ Real.sin ψ = s * (z 0).im ∧
      Real.cos (ψ + t₁) = (z 1).re ∧ Real.sin (ψ + t₁) = s * (z 1).im ∧
      Real.cos (ψ + t₂) = (z 2).re ∧ Real.sin (ψ + t₂) = s * (z 2).im := by
  have h0 : z 0 ≠ 0 := by
    intro he
    have hh := hz 0
    simp [he] at hh
  have h10 : z 1 ≠ z 0 := by
    intro he
    have hh := congrArg Fin.val (hinj he)
    norm_num at hh
  have h20 : z 2 ≠ z 0 := by
    intro he
    have hh := congrArg Fin.val (hinj he)
    norm_num at hh
  have h12 : z 1 ≠ z 2 := by
    intro he
    have hh := congrArg Fin.val (hinj he)
    norm_num at hh
  have hn1 : z 1 / z 0 ≠ 1 := by
    intro he
    apply h10
    calc
      z 1 = (z 1 / z 0) * z 0 := (div_mul_cancel₀ _ h0).symm
      _ = z 0 := by rw [he, one_mul]
  have hn2 : z 2 / z 0 ≠ 1 := by
    intro he
    apply h20
    calc
      z 2 = (z 2 / z 0) * z 0 := (div_mul_cancel₀ _ h0).symm
      _ = z 0 := by rw [he, one_mul]
  have hne : z 1 / z 0 ≠ z 2 / z 0 := by
    intro he
    apply h12
    have hh := congrArg (fun w : ℂ => w * z 0) he
    simpa only [div_mul_cancel₀ _ h0] using hh
  obtain ⟨s, a, b, hs, ha0, hab, hbp, hac, has, hbc, hbs⟩ :=
    f6_ordered_angles (z 1 / z 0) (z 2 / z 0)
      (by simp [norm_div, hz]) (by simp [norm_div, hz]) hn1 hn2 hne
  have hs2 : s * s = 1 := by
    rcases hs with hs | hs <;> rw [hs] <;> norm_num
  have hc0 : Real.cos (z 0).arg = (z 0).re := by
    simpa [hz 0] using Complex.norm_mul_cos_arg (z 0)
  have hi0 : Real.sin (z 0).arg = (z 0).im := by
    simpa [hz 0] using Complex.norm_mul_sin_arg (z 0)
  have base : ∃ ψ : ℝ, Real.cos ψ = (z 0).re ∧ Real.sin ψ = s * (z 0).im := by
    rcases hs with he | he
    · refine ⟨(z 0).arg, hc0, ?_⟩
      simpa [he] using hi0
    · refine ⟨-(z 0).arg, ?_, ?_⟩
      · simpa using hc0
      · simpa [he] using congrArg Neg.neg hi0
  obtain ⟨ψ, hψc, hψs⟩ := base
  have rotate (w : ℂ) (t : ℝ) (htc : Real.cos t = w.re)
      (hts : Real.sin t = s * w.im) :
      Real.cos (ψ + t) = (w * z 0).re ∧
      Real.sin (ψ + t) = s * (w * z 0).im := by
    constructor
    · rw [Real.cos_add, hψc, hψs, htc, hts, Complex.mul_re]
      calc
        (z 0).re * w.re - (s * (z 0).im) * (s * w.im) =
            w.re * (z 0).re - (s * s) * (w.im * (z 0).im) := by ring
        _ = w.re * (z 0).re - w.im * (z 0).im := by rw [hs2, one_mul]
    · rw [Real.sin_add, hψc, hψs, htc, hts, Complex.mul_im]
      ring
  have hrot1 := rotate (z 1 / z 0) a hac has
  have hrot2 := rotate (z 2 / z 0) b hbc hbs
  rw [div_mul_cancel₀ _ h0] at hrot1 hrot2
  exact ⟨s, ψ, a, b, hs, ha0, hab, hbp, hψc, hψs,
    hrot1.1, hrot1.2, hrot2.1, hrot2.2⟩

set_option autoImplicit false
open MeasureTheory Real SphereGeom

theorem proof_SolidGeom_triple_normal_form (c : Fin 3 → E3)
    (hQ : 0 < 4 * dist (c 0) (c 1) ^ 2 * dist (c 0) (c 2) ^ 2
        - (dist (c 0) (c 1) ^ 2 + dist (c 0) (c 2) ^ 2 - dist (c 1) (c 2) ^ 2) ^ 2
        - dist (c 0) (c 1) ^ 2 * dist (c 0) (c 2) ^ 2 * dist (c 1) (c 2) ^ 2) :
    ∃ (o : E3) (e : Fin 3 → E3) (R ψ α₀ α₁ α₂ : ℝ), Orthonormal ℝ e ∧ 0 < R ∧ R < 1 ∧
      0 < α₀ ∧ 0 < α₁ ∧ 0 < α₂ ∧ α₀ + α₁ + α₂ = π ∧
      c 0 = o - R • (cos ψ • e 0 + sin ψ • e 1) ∧
      c 1 = o - R • (cos (ψ + 2 * α₂) • e 0 + sin (ψ + 2 * α₂) • e 1) ∧
      c 2 = o - R • (cos (ψ + 2 * α₂ + 2 * α₀) • e 0 + sin (ψ + 2 * α₂ + 2 * α₀) • e 1)  := by
  classical
  have h01 : c 0 ≠ c 1 := by
    intro h
    simp [h] at hQ
  have h02 : c 0 ≠ c 2 := by
    intro h
    simp [h, dist_comm] at hQ
  have h12 : c 1 ≠ c 2 := by
    intro h
    simp only [h, dist_self, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at hQ
    nlinarith
  have hc : Function.Injective c := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨o,R,hR,hR1,hn,hp,hli⟩ := f6_circumcircle_data c hQ
  obtain ⟨e,z,he,hz,hzi,hcform⟩ :=
    f6_circle_coordinates c o (c 1-c 0) (c 2-c 0) R hR hc hn hp
  have ha := f6_three_angles z hz hzi
  obtain ⟨s,ψ,t₁,t₂,hs,ht₁,ht₁₂,ht₂,hcos0,hsin0,hcos1,hsin1,hcos2,hsin2⟩ := ha
  let e' : Fin 3 → E3 := ![e 0,s • e 1,e 2]
  have hs2 : s*s=1 := by rcases hs with rfl | rfl <;> norm_num
  have hen := he.1
  have hns : |s|=1 := by rcases hs with rfl | rfl <;> norm_num
  have he' : Orthonormal ℝ e' := by
    rw [orthonormal_iff_ite] at he ⊢
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e', inner_smul_left, inner_smul_right, he, hen, norm_smul, hns, ← mul_assoc, hs2]
  have harg1 : ψ + 2 * (t₁/2) = ψ+t₁ := by ring
  have harg2 : ψ + 2 * (t₁/2) + 2 * ((t₂-t₁)/2) = ψ+t₂ := by ring
  have hsum : (t₂-t₁)/2 + (π-t₂/2) + t₁/2 = π := by ring
  refine ⟨o,e',R,ψ,(t₂-t₁)/2,π-t₂/2,t₁/2,he',hR,hR1,
    by linarith,by linarith,by linarith,hsum,?_,?_,?_⟩
  · apply (eq_sub_iff_add_eq).mpr
    change c 0 + R • (cos ψ • e 0 + sin ψ • (s • e 1)) = o
    rw [hcos0, hsin0, smul_smul]
    have hscale : s * (z 0).im * s = (z 0).im := by
      calc s * (z 0).im * s = (z 0).im * (s*s) := by ring
           _ = (z 0).im := by rw [hs2, mul_one]
    rw [hscale, ← hcform 0]
    abel
  · apply (eq_sub_iff_add_eq).mpr
    change c 1 + R • (cos (ψ+2*(t₁/2)) • e 0 + sin (ψ+2*(t₁/2)) • (s • e 1)) = o
    rw [harg1, hcos1, hsin1, smul_smul]
    have hscale : s * (z 1).im * s = (z 1).im := by
      calc s * (z 1).im * s = (z 1).im * (s*s) := by ring
           _ = (z 1).im := by rw [hs2, mul_one]
    rw [hscale, ← hcform 1]
    abel
  · apply (eq_sub_iff_add_eq).mpr
    change c 2 + R • (cos (ψ+2*(t₁/2)+2*((t₂-t₁)/2)) • e 0 +
      sin (ψ+2*(t₁/2)+2*((t₂-t₁)/2)) • (s • e 1)) = o
    rw [harg2, hcos2, hsin2, smul_smul]
    have hscale : s * (z 2).im * s = (z 2).im := by
      calc s * (z 2).im * s = (z 2).im * (s*s) := by ring
           _ = (z 2).im := by rw [hs2, mul_one]
    rw [hscale, ← hcform 2]
    abel
