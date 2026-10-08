import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

open MeasureTheory SphereGeom
open scoped Classical
noncomputable section

theorem proof_SphereGeom_Aux_Crofton_measurable_encard_greatCircle_compact (K : Set E3) (hK : IsCompact K) :
    Measurable (fun p : E3 => ((greatCircle p ∩ K).encard : ENNReal)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have htuple (p : E3) (n : ℕ) :
      (n : ENat) ≤ (greatCircle p ∩ K).encard ↔
        ∃ x : Fin n → K, (∀ i, (x i : E3) ∈ greatCircle p) ∧ Function.Injective x := by
    constructor
    · intro hc
      have hu : (Set.univ : Set (Fin n)).encard ≤ (greatCircle p ∩ K).encard := by
        simpa only [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] using hc
      obtain ⟨f, hf, hinj⟩ := (Set.finite_univ (α := Fin n)).exists_injOn_of_encard_le hu
      let x : Fin n → K := fun i => ⟨f i, (hf (Set.mem_univ i)).2⟩
      refine ⟨x, fun i => (hf (Set.mem_univ i)).1, ?_⟩
      intro i j hij
      apply hinj (Set.mem_univ i) (Set.mem_univ j)
      exact congrArg (fun z : K => (z : E3)) hij
    · rintro ⟨x, hx, hinj⟩
      have hv : Function.Injective (fun i => (x i : E3)) := Subtype.val_injective.comp hinj
      have hc := Set.encard_le_encard_of_injOn
        (show Set.MapsTo (fun i => (x i : E3)) Set.univ (greatCircle p ∩ K) from
          fun i _ => ⟨hx i, (x i).property⟩) hv.injOn
      simpa only [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] using hc
  have hseparate (n : ℕ) (x : Fin n → K) (hx : Function.Injective x) :
      ∃ k : ℕ, ∀ i j, i ≠ j → (1 : ℝ) / (k + 1 : ℝ) ≤ dist (x i : E3) (x j : E3) := by
    let Q := {ij : Fin n × Fin n // ij.1 ≠ ij.2}
    have hp (q : Q) : 0 < dist (x q.1.1 : E3) (x q.1.2 : E3) := by
      apply dist_pos.mpr
      intro heq
      exact q.2 (hx (Subtype.ext heq))
    let r : Q → ℕ := fun q => (exists_nat_one_div_lt (hp q)).choose
    have hr (q : Q) : (1 : ℝ) / (r q + 1 : ℝ) < dist (x q.1.1 : E3) (x q.1.2 : E3) :=
      (exists_nat_one_div_lt (hp q)).choose_spec
    obtain ⟨k, hk⟩ := Finite.exists_le r
    refine ⟨k, fun i j hij => ?_⟩
    let q : Q := ⟨(i, j), hij⟩
    have hden : (r q + 1 : ℝ) ≤ (k + 1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right (hk q) 1
    exact (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < r q + 1) hden).trans (hr q).le
  let C (n k : ℕ) : Set (E3 × (Fin n → K)) :=
    {z | (∀ i, ‖(z.2 i : E3)‖ = 1 ∧ inner ℝ z.1 (z.2 i : E3) = 0) ∧
      ∀ i j, i ≠ j → (1 : ℝ) / (k + 1 : ℝ) ≤ dist (z.2 i : E3) (z.2 j : E3)}
  have hC (n k : ℕ) : IsClosed (C n k) := by
    have hc (i : Fin n) : Continuous (fun z : E3 × (Fin n → K) => (z.2 i : E3)) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
    change IsClosed
      ({z : E3 × (Fin n → K) | ∀ i, ‖(z.2 i : E3)‖ = 1 ∧ inner ℝ z.1 (z.2 i : E3) = 0} ∩
        {z | ∀ i j, i ≠ j → (1 : ℝ) / (k + 1 : ℝ) ≤ dist (z.2 i : E3) (z.2 j : E3)})
    refine IsClosed.inter ?_ ?_
    · simp only [Set.setOf_forall]
      apply isClosed_iInter
      intro i
      exact (isClosed_eq (hc i).norm continuous_const).inter
        (isClosed_eq (continuous_fst.inner (hc i)) continuous_const)
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le continuous_const ((hc i).dist (hc j))
  let T (n k : ℕ) : Set E3 := Prod.fst '' C n k
  have hT (n k : ℕ) : IsClosed (T n k) :=
    isClosedMap_fst_of_compactSpace (C n k) (hC n k)
  have hlevel (n : ℕ) :
      {p : E3 | (n : ENat) ≤ (greatCircle p ∩ K).encard} = ⋃ k : ℕ, T n k := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hp
      obtain ⟨x, hx, hinj⟩ := (htuple p n).mp hp
      obtain ⟨k, hsep⟩ := hseparate n x hinj
      refine ⟨k, ⟨(p, x), ?_, rfl⟩⟩
      exact ⟨fun i => hx i, hsep⟩
    · rintro ⟨k, ⟨⟨p', x⟩, hx, heq⟩⟩
      change p' = p at heq
      subst p'
      apply (htuple p n).mpr
      refine ⟨x, fun i => hx.1 i, ?_⟩
      intro i j heq
      by_contra hij
      have hdist := hx.2 i j hij
      change (1 : ℝ) / (k + 1 : ℝ) ≤ dist (x i : E3) (x j : E3) at hdist
      rw [heq, dist_self] at hdist
      have hpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
      linarith
  have hmlevel (n : ℕ) : MeasurableSet {p : E3 | (n : ENat) ≤ (greatCircle p ∩ K).encard} := by
    rw [hlevel]
    exact MeasurableSet.iUnion (fun k => (hT n k).measurableSet)
  have hsingleton (c : ENat) (n : ℕ) :
      c = (n : ENat) ↔ (n : ENat) ≤ c ∧ ¬((n + 1 : ℕ) : ENat) ≤ c := by
    cases c with
    | top => simp
    | coe m =>
      simp only [ENat.some_eq_natCast, ENat.natCast_le_natCast, ENat.natCast_inj]
      omega
  have hmeas : Measurable (fun p : E3 => (greatCircle p ∩ K).encard) := by
    apply ENat.measurable_iff.mpr
    intro n
    have hs : (fun p : E3 => (greatCircle p ∩ K).encard) ⁻¹' {(n : ENat)} =
        {p | (n : ENat) ≤ (greatCircle p ∩ K).encard} \
          {p | ((n + 1 : ℕ) : ENat) ≤ (greatCircle p ∩ K).encard} := by
      ext p
      exact hsingleton _ n
    rw [hs]
    exact (hmlevel n).diff (hmlevel (n + 1))
  exact (measurable_of_countable (fun c : ENat => (c : ENNReal))).comp hmeas

#print axioms proof_SphereGeom_Aux_Crofton_measurable_encard_greatCircle_compact
