import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_area_sectors_boundary_sum
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_tailAngle
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

theorem SolidGeom.CapPolar.area_sectors_boundary_sum :
    ∀ (n : ℕ) (p : SphereGeom.E3)
    (a b : Fin (n+1) → SphereGeom.E3) (A h α ω : Fin (n+1) → ℝ)
    (hh : ∀ j, 0<h j) (hA : ∀ j, h j<A j) (hA1 : ∀ j, A j≤1)
    (hp : inner ℝ p p=1) (ha : ∀ j, inner ℝ (a j) (a j)=1)
    (hpa : ∀ j, inner ℝ p (a j)=0) (hb : ∀ j, SphereGeom.cross p (a j)=b j)
    (hglue : ∀ j, SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (ω j)=
      SolidGeom.CapPolar.capExitPoint p (a (j+1)) (b (j+1)) (A (j+1)) (h (j+1)) (α (j+1))), (∑ j : Fin (n+1), ∫ ψ in (α j)..(ω j), SolidGeom.CapPolar.areaDensity (A j) (h j) ψ)=
      (∑ j : Fin (n+1), (ω j-α j))-
      (∑ j : Fin (n+1), h j*(SolidGeom.CapPolar.momentAzimuth (A j) (h j) (ω j)-
        SolidGeom.CapPolar.momentAzimuth (A j) (h j) (α j)))-
      (∑ j : Fin (n+1), SolidGeom.CapPolar.capCorner (SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (ω j))
        (SolidGeom.CapPolar.capAxis p (a j) (A j))
        (SolidGeom.CapPolar.capAxis p (a (j+1)) (A (j+1)))) :=
  @proof_SolidGeom_CapPolar_area_sectors_boundary_sum
