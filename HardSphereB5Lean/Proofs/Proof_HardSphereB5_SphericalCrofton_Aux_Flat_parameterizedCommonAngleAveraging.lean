import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Flat_commonAngleAveraging
set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

theorem proof_HardSphereB5_SphericalCrofton_Aux_Flat_parameterizedCommonAngleAveraging
    {α : Type*} [MeasurableSpace α] (η : Measure α) [SFinite η]
    (T : ℝ) (hT : 0 < T) (Q : α × (ℝ × ℝ) → ℝ)
    (hQ : Integrable Q (η.prod ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T)))))
    (hper : ∀ x : α, Function.Periodic (fun χ : ℝ => Q (x, (0, χ))) T)
    (hdiag : ∀ (x : α) (a b t : ℝ), Q (x, (a + t, b + t)) = Q (x, (a, b))) :
    Integrable (fun p : α × ℝ => Q (p.1, (0, p.2)))
      (η.prod (volume.restrict (Ioc (-(T / 2)) (T / 2)))) ∧
      (∫ p, Q p ∂(η.prod ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))))) =
        T * ∫ p : α × ℝ, Q (p.1, (0, p.2))
          ∂(η.prod (volume.restrict (Ioc (-(T / 2)) (T / 2)))) := by
  letI : Fact (0 < T) := ⟨hT⟩
  let μT : Measure ℝ := volume.restrict (Ioc 0 T)
  have hrep (x : α) (a b : ℝ) : Q (x, (a, b)) = Q (x, (0, b - a)) := by
    simpa only [add_neg_cancel, sub_eq_add_neg] using (hdiag x a b (-a)).symm
  have h1 : Integrable (fun p : (α × ℝ) × ℝ => Q (p.1.1, (p.1.2, p.2)))
      ((η.prod μT).prod μT) :=
    (measurePreserving_prodAssoc η μT μT).integrable_comp_of_integrable hQ
  have h2 : Integrable (fun p : (ℝ × α) × ℝ => Q (p.1.2, (p.1.1, p.2)))
      ((μT.prod η).prod μT) :=
    ((Measure.measurePreserving_swap (μ := μT) (ν := η)).prod
      (MeasurePreserving.id μT)).integrable_comp_of_integrable h1
  have h3 : Integrable (fun p : ℝ × (α × ℝ) => Q (p.2.1, (p.1, p.2.2)))
      (μT.prod (η.prod μT)) :=
    ((measurePreserving_prodAssoc μT η μT).integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding).mp h2
  have hvol : volume (Ioc (0 : ℝ) T) ≠ 0 := by
    simpa only [Real.volume_Ioc, sub_zero, ENNReal.ofReal_ne_zero_iff] using hT
  obtain ⟨a, _, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol h3.prod_right_ae
  let H : α × AddCircle T → ℝ := fun p => ((hper p.1).sub_const a).lift p.2
  have hHval (x : α) (z : AddCircle T) :
      H (x, z) = Q (x, (a, (AddCircle.equivIoc T 0 z : ℝ))) := by
    have hz : ((AddCircle.equivIoc T 0 z : ℝ) : AddCircle T) = z :=
      AddCircle.coe_equivIoc
    calc
      H (x, z) = H (x, ((AddCircle.equivIoc T 0 z : ℝ) : AddCircle T)) := by rw [hz]
      _ = Q (x, (0, (AddCircle.equivIoc T 0 z : ℝ) - a)) := by
        exact Function.Periodic.lift_coe ((hper x).sub_const a) _
      _ = Q (x, (a, (AddCircle.equivIoc T 0 z : ℝ))) := (hrep x a _).symm
  have hwrap : MeasurePreserving (fun z : AddCircle T => (AddCircle.equivIoc T 0 z : ℝ))
      volume μT := by
    simpa only [Function.comp_def, zero_add] using
      (measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
        (s := Ioc 0 (0 + T)) measurableSet_Ioc).comp
        (AddCircle.measurePreserving_equivIoc T (a := 0))
  have hH : Integrable H (η.prod (volume : Measure (AddCircle T))) := by
    have h := ((MeasurePreserving.id η).prod hwrap).integrable_comp_of_integrable ha
    convert h using 1
    funext p
    exact hHval p.1 p.2
  have hmk : MeasurePreserving (fun χ : ℝ => (χ : AddCircle T))
      (volume.restrict (Ioc (-(T / 2)) (T / 2))) volume := by
    convert AddCircle.measurePreserving_mk T (-(T / 2)) using 1 <;> congr 1 <;> ring
  have hshift : MeasurePreserving (fun χ : ℝ => (χ : AddCircle T) + (a : AddCircle T))
      (volume.restrict (Ioc (-(T / 2)) (T / 2))) volume :=
    (measurePreserving_add_right (volume : Measure (AddCircle T)) (a : AddCircle T)).comp hmk
  have hq : Integrable (fun p : α × ℝ => Q (p.1, (0, p.2)))
      (η.prod (volume.restrict (Ioc (-(T / 2)) (T / 2)))) := by
    have h := ((MeasurePreserving.id η).prod hshift).integrable_comp_of_integrable hH
    convert h using 1
    funext p
    change Q (p.1, (0, p.2)) =
      ((hper p.1).sub_const a).lift ((p.2 : AddCircle T) + (a : AddCircle T))
    rw [← AddCircle.coe_add, Function.Periodic.lift_coe]
    simp only [add_sub_cancel_right]
  refine ⟨hq, ?_⟩
  have hid : (fun x : α => ∫ p : ℝ × ℝ, Q (x, p) ∂(μT.prod μT)) =ᵐ[η]
      (fun x : α => T * ∫ χ in Ioc (-(T / 2)) (T / 2), Q (x, (0, χ))) := by
    filter_upwards [hQ.prod_right_ae] with x hx
    exact (HardSphereB5.SphericalCrofton.Aux.Flat.commonAngleAveraging T hT
      (fun p => Q (x, p)) hx (hper x) (hdiag x)).2
  rw [MeasureTheory.integral_prod Q hQ, integral_congr_ae hid, integral_const_mul,
    MeasureTheory.integral_prod _ hq]
