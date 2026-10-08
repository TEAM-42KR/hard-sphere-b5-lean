import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_cyclic_sector_moment_boundary_sum
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
set_option autoImplicit false
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
noncomputable section

theorem SolidGeom.CapPolar.cyclic_sector_moment_boundary_sum :
    ∀ (n : ℕ) (p : E3)
    (a b : Fin (n+1) → E3) (A h α ω : Fin (n+1) → ℝ)
    (hh : ∀ j, 0<h j) (hA : ∀ j, h j<A j) (hA1 : ∀ j, A j≤1)
    (hf : ∀ j, Orthonormal ℝ (fun k : Fin 3 => ![p,a j,b j] k))
    (hp : inner ℝ p p=1) (ha : ∀ j, inner ℝ (a j) (a j)=1)
    (hpa : ∀ j, inner ℝ p (a j)=0) (hpb : ∀ j, inner ℝ p (b j)=0)
    (hb : ∀ j, SphereGeom.cross p (a j)=b j)
    (hglue : ∀ j, SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (ω j) =
      SolidGeom.CapPolar.capExitPoint p (a (j+1)) (b (j+1)) (A (j+1)) (h (j+1)) (α (j+1))), (∑ j, ∫ ψ in (α j)..(ω j), ∫ ρ in (0)..(exitRadius (A j) (h j) ψ),
      Real.sin ρ • polarRay p (a j) (b j) ψ ρ) =
    ∑ j, (((1-(h j)^2)*
        (momentAzimuth (A j) (h j) (ω j)-momentAzimuth (A j) (h j) (α j))/2) •
          SolidGeom.CapPolar.capAxis p (a j) (A j) +
      (h j/2) • SphereGeom.cross (SolidGeom.CapPolar.capAxis p (a j) (A j))
        (SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (ω j)-
          SolidGeom.CapPolar.capExitPoint p (a j) (b j) (A j) (h j) (α j))) :=
  @proof_SolidGeom_CapPolar_cyclic_sector_moment_boundary_sum
