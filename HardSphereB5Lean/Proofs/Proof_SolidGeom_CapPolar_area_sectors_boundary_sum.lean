import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_tailAngle
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_cap_corner_tail_angle
import HardSphereB5Lean.Theorems.Thm_SolidGeom_CapPolar_sector_area_primitive
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
open scoped RealInnerProductSpace
set_option maxHeartbeats 1000000
private lemma SolidGeom.CapPolar.A4_primitive_boundary_form (A h ψ : ℝ) :
    areaPrimitive A h ψ=ψ-h*momentAzimuth A h ψ+tailAngle A h ψ := by
  unfold areaPrimitive tailPrimitive momentAzimuth tailAngle rayRadical
  ring
theorem proof_SolidGeom_CapPolar_area_sectors_boundary_sum (n : ℕ) (p : SphereGeom.E3)
    (a b : Fin (n+1) → SphereGeom.E3) (A h α ω : Fin (n+1) → ℝ)
    (hh : ∀ j, 0<h j) (hA : ∀ j, h j<A j) (hA1 : ∀ j, A j≤1)
    (hp : inner ℝ p p=1) (ha : ∀ j, inner ℝ (a j) (a j)=1)
    (hpa : ∀ j, inner ℝ p (a j)=0) (hb : ∀ j, SphereGeom.cross p (a j)=b j)
    (hglue : ∀ j, SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (ω j)=
      SolidGeom.CapPolar.capExitPoint p (a (j+1)) (b (j+1)) (A (j+1)) (h (j+1)) (α (j+1))) :
    (∑ j : Fin (n+1), ∫ ψ in (α j)..(ω j), SolidGeom.CapPolar.areaDensity (A j) (h j) ψ)=
      (∑ j : Fin (n+1), (ω j-α j))-
      (∑ j : Fin (n+1), h j*(SolidGeom.CapPolar.momentAzimuth (A j) (h j) (ω j)-
        SolidGeom.CapPolar.momentAzimuth (A j) (h j) (α j)))-
      (∑ j : Fin (n+1), SolidGeom.CapPolar.capCorner (SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (ω j))
        (SolidGeom.CapPolar.capAxis p (a j) (A j))
        (SolidGeom.CapPolar.capAxis p (a (j+1)) (A (j+1))))  := by
  have hc : ∀ j, capCorner (capExitPoint p (a j) (b j) (A j) (h j) (ω j))
      (capAxis p (a j) (A j)) (capAxis p (a (j+1)) (A (j+1)))=
      tailAngle (A (j+1)) (h (j+1)) (α (j+1))-tailAngle (A j) (h j) (ω j) := by
    intro j
    exact cap_corner_tail_angle p (a j) (b j) (a (j+1)) (b (j+1))
      (A j) (h j) (ω j) (A (j+1)) (h (j+1)) (α (j+1)) hp
      (ha j) (hpa j) (hb j) (ha (j+1)) (hpa (j+1)) (hb (j+1))
      (hh j) (hA j) (hA1 j) (hh (j+1)) (hA (j+1)) (hA1 (j+1)) (hglue j)
  have hperm : (∑ j : Fin (n+1), tailAngle (A (j+1)) (h (j+1)) (α (j+1)))=
      ∑ j : Fin (n+1), tailAngle (A j) (h j) (α j) := by
    exact Fintype.sum_equiv (Equiv.addRight (1 : Fin (n+1))) _ _ (fun j => rfl)
  have hterm : ∀ j, (∫ ψ in (α j)..(ω j), areaDensity (A j) (h j) ψ)=
      (ω j-α j)-h j*(momentAzimuth (A j) (h j) (ω j)-momentAzimuth (A j) (h j) (α j))+
      (tailAngle (A j) (h j) (ω j)-tailAngle (A j) (h j) (α j)) := by
    intro j
    rw [sector_area_primitive (A j) (h j) (α j) (ω j) (hh j) (hA j) (hA1 j),
      A4_primitive_boundary_form,A4_primitive_boundary_form]
    ring
  simp_rw [hterm,hc]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,hperm]
  ring
#print axioms proof_SolidGeom_CapPolar_area_sectors_boundary_sum
