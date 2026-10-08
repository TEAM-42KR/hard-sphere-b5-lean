import Mathlib
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Santalo_Charts
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Santalo_santaloMixed
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Santalo_gram_mixed
set_option autoImplicit false
noncomputable section
open SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Santalo
open HardSphereB5.Lean (Pt e)

private lemma cross_triples (a b u v : Pt) :
    inner ℝ (cross a u) v = inner ℝ a (cross u v) ∧
    inner ℝ u (-cross b v) = inner ℝ b (cross u v) ∧
    inner ℝ (cross a u) (-cross b v) =
      inner ℝ a v * inner ℝ b u - inner ℝ a b * inner ℝ u v := by
  have hi (p q : Pt) : inner ℝ p q = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]; ring
  simp_rw [hi]
  simp only [SphereGeom.cross, WithLp.ofLp_toLp, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    PiLp.neg_apply]
  constructor
  · ring
  constructor <;> ring

theorem proof_HardSphereB5_SphericalCrofton_Aux_Santalo_mixed_distance_identity (D : Pt) (C : Charts) (hC : IsChart D C)
    (t s : ℝ) (ht : t ∈ Set.Icc 0 C.TA) (hs : s ∈ Set.Icc 0 C.TB)
    (hx : inner ℝ (u D C t) (v D C s) ∈ Set.Ioo (-1) 1) :
    -deriv (fun z => deriv (delta D C z) s) t =
      (inner ℝ (nAv D) (v D C s) - inner ℝ (nAv D) (u D C t) * inner ℝ (u D C t) (v D C s)) *
      (inner ℝ (nBv D) (u D C t) - inner ℝ (nBv D) (v D C s) * inner ℝ (u D C t) (v D C s)) /
      (Real.sin (Real.arccos (inner ℝ (u D C t) (v D C s))) ^ 3) := by
  rcases hC with ⟨_, _, _, _, _, _, _, _, hA, hB, hdu, hdv⟩
  have hut : u D C t ∈ arcA D := by rw [hA]; exact ⟨t, ht, rfl⟩
  have hvs : v D C s ∈ arcB D := by rw [hB]; exact ⟨s, hs, rfl⟩
  have hu : ‖u D C t‖ = 1 := by
    unfold arcA at hut
    split_ifs at hut with hz
    · simpa using hut
    · exact hut.1.1
  have hv : ‖v D C s‖ = 1 := by
    unfold arcB at hvs
    split_ifs at hvs with hz
    · simpa using hvs
    · exact hvs.1.1
  let X : ℝ → ℝ → ℝ := fun p q => inner ℝ (u D C q) (v D C p)
  let X1 : ℝ → ℝ := fun q => inner ℝ (u D C q) (-cross (nBv D) (v D C s))
  let x2 := inner ℝ (cross (nAv D) (u D C t)) (v D C s)
  let x12 := inner ℝ (cross (nAv D) (u D C t)) (-cross (nBv D) (v D C s))
  let L1 := inner ℝ (nAv D) (v D C s) - inner ℝ (nAv D) (u D C t) * inner ℝ (u D C t) (v D C s)
  let L2 := inner ℝ (nBv D) (u D C t) - inner ℝ (nBv D) (v D C s) * inner ℝ (u D C t) (v D C s)
  have h1 : ∀ q, HasDerivAt (fun p => X p q) (X1 q) s := by
    intro q
    simpa [X, X1] using (hasDerivAt_const s (u D C q)).inner ℝ (hdv s)
  have h2 : HasDerivAt (X s) x2 t :=
    by simpa [X, x2] using (hdu t).inner ℝ (hasDerivAt_const t (v D C s))
  have h12 : HasDerivAt X1 x12 t :=
    by simpa [X1, x12] using (hdu t).inner ℝ (hasDerivAt_const t (-cross (nBv D) (v D C s)))
  have htrip := cross_triples (nAv D) (nBv D) (u D C t) (v D C s)
  have hGram : (1 - X s t ^ 2) * x12 + X s t * X1 t * x2 = L1 * L2 := by
    dsimp [X, X1, x2, x12, L1, L2]
    rw [htrip.1, htrip.2.1, htrip.2.2]
    convert SphereGeom.Aux.Santalo.gram_mixed (nAv D) (nBv D) (u D C t) (v D C s) hu hv using 1 <;> ring
  have hbase := HardSphereB5.Lean.Santalo.santaloMixed X X1 s t x2 x12 L1 L2 hx h1 h2 h12 hGram
  have hsq : Real.sqrt (1 - inner ℝ (u D C t) (v D C s) ^ 2) ^ 2 =
      1 - inner ℝ (u D C t) (v D C s) ^ 2 := Real.sq_sqrt (by nlinarith [hx.1, hx.2])
  have hden : Real.sin (Real.arccos (inner ℝ (u D C t) (v D C s))) ^ 3 =
      (1 - inner ℝ (u D C t) (v D C s) ^ 2) * Real.sqrt (1 - inner ℝ (u D C t) (v D C s) ^ 2) := by
    rw [Real.sin_arccos]
    calc
      _ = Real.sqrt (1 - inner ℝ (u D C t) (v D C s) ^ 2) ^ 2 *
          Real.sqrt (1 - inner ℝ (u D C t) (v D C s) ^ 2) := by ring
      _ = _ := by rw [hsq]
  dsimp [X, L1, L2] at hbase
  rw [← hden] at hbase
  exact hbase
