import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
set_option autoImplicit false

noncomputable section
open MeasureTheory Real SphereGeom

namespace HardSphereB5.SphericalCrofton

open HardSphereB5.Lean (Pt e)
open scoped Classical

def len (A : Set Pt) : ℝ := (arcMeasure A).toReal

def chordLen (K G : Set Pt) : ℝ := len (G ∩ K)

def sArea (K : Set Pt) : ℝ := (dOmega K).toReal

def sFrontier (K : Set Pt) : Set Pt :=
  Subtype.val '' frontier ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' K)

def sInterior (K : Set Pt) : Set Pt :=
  Subtype.val '' interior ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' K)

def perim (K : Set Pt) : ℝ := len (sFrontier K)

structure IsRegularRegionCrofton (K : Set Pt) : Prop where
  subset_sphere : K ⊆ Metric.sphere (0 : Pt) 1
  isCompact : IsCompact K
  eq_closure_interior : K = closure (sInterior K)
  interior_nonempty : (sInterior K).Nonempty
  geodesically_convex : ∀ u ∈ K, ∀ v ∈ K, u ≠ -v → ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(1 - t) • u + t • v‖⁻¹ • ((1 - t) • u + t • v) ∈ K
  in_closed_hemisphere : ∃ n : Pt, n ≠ 0 ∧ ∀ u ∈ K, 0 ≤ inner ℝ n u
  boundary_C2_arcs : ∃ (N : ℕ) (γ : Fin N → ℝ → Pt), (∀ m, ContDiff ℝ 2 (γ m)) ∧
    (∀ m, Set.InjOn (γ m) (Set.Icc 0 1)) ∧ (∀ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (γ m) t ≠ 0) ∧
    sFrontier K = ⋃ m, γ m '' Set.Icc 0 1
  finite_perimeter : arcMeasure (sFrontier K) < ⊤

inductive Kern
  | one
  | cos

def wK : Kern → ℝ → ℝ
  | .one, _ => 1
  | .cos, x => x

def phiK : Kern → ℝ → ℝ
  | .one, L => L - 2 * Real.sin L + √3 - π / 3
  | .cos, L => π / 12 + √3 / 8 - L / 4 - Real.sin (2 * L) / 4

def cA : Kern → ℝ
  | .one => π
  | .cos => 3 * π / 4

def cP : Kern → ℝ
  | .one => √3 - π / 3
  | .cos => √3 / 8 + π / 12

def alphaK (f : Kern) : ℝ := 2 * ∫ t in (0 : ℝ)..(π / 3), wK f (Real.cos t) * Real.sin t

def bK (f : Kern) : ℝ := 2 * ∫ t in (0 : ℝ)..(π / 3), t * wK f (Real.cos t) * Real.sin t

def kK (f : Kern) (L : ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..(min L (π / 3)), (L - t) * wK f (Real.cos t) * Real.sin t

def Ff (f : Kern) (K : Set Pt) : ℝ :=
  ∫ u in K, ∫ v in K, wK f (inner ℝ u v) * (if 1 / 2 ≤ inner ℝ u v then 1 else 0) ∂dOmega ∂dOmega

def Rf (f : Kern) (K : Set Pt) : ℝ :=
  gcIntegral fun G => if 0 < chordLen K G ∧ chordLen K G < π / 3 then phiK f (chordLen K G) else 0

def RfAll (f : Kern) (K : Set Pt) : ℝ :=
  gcIntegral fun G => if chordLen K G < π / 3 then phiK f (chordLen K G) else 0

def LamC : Set Pt := Metric.closedBall 0 1 ∩ Metric.closedBall e 1

def SigmaD (D : Pt) : Set Pt := {u | ‖u‖ = 1 ∧ D + u ∈ LamC}

def Rc (a b : ℝ) : ℝ := a * b / √((a + b + 1) * (a + b - 1) * (a - b + 1) * (-a + b + 1))

def offAxis (D : Pt) : Prop := ∀ t : ℝ, D ≠ t • e

def vertsD (D : Pt) : Set Pt := {u | ‖u‖ = 1 ∧ ‖D + u‖ = 1 ∧ dist (D + u) e = 1}

def Jnear (f : Kern) : ℝ :=
  ∫ D in LamC, (∫ C in LamC, ∫ E in LamC,
    wK f (inner ℝ (C - D) (E - D)) * (if dist C E ≤ 1 then 1 else 0)
      ∂(sphereMeasure D) ∂(sphereMeasure D))

def ECr (f : Kern) : ℝ :=
  cA f * (∫ D in LamC, sArea (SigmaD D)) - cP f * (∫ D in LamC, perim (SigmaD D))

def nAv (D : Pt) : Pt := (‖D‖)⁻¹ • (-D)

def nBv (D : Pt) : Pt := (‖D - e‖)⁻¹ • (e - D)

def arcA (D : Pt) : Set Pt := if D = 0 then ∅ else {u | u ∈ SigmaD D ∧ ‖D + u‖ = 1}

def arcB (D : Pt) : Set Pt := if D = e then ∅ else {u | u ∈ SigmaD D ∧ dist (D + u) e = 1}

def unitDir (v : Pt) : Pt := (‖v‖)⁻¹ • v

def tanA (D u : Pt) : Pt := unitDir (cross (nAv D) u)

def tanB (D v : Pt) : Pt := unitDir (cross (nBv D) v)

def santaloDens (u v τ1 τ2 : Pt) : ℝ :=
  |inner ℝ (cross u v) τ1| * |inner ℝ (cross u v) τ2| / Real.sin (arccos (inner ℝ u v)) ^ 3

def cutKern (f : Kern) (δ : ℝ) : ℝ := if δ < π / 3 then phiK f δ else 0

def AAf (f : Kern) (D : Pt) : ℝ :=
  (1 / 2) * ∫ u in arcA D, ∫ v in arcA D,
    cutKern f (arccos (inner ℝ u v)) * santaloDens u v (tanA D u) (tanA D v) ∂arcMeasure ∂arcMeasure

def BBf (f : Kern) (D : Pt) : ℝ :=
  (1 / 2) * ∫ u in arcB D, ∫ v in arcB D,
    cutKern f (arccos (inner ℝ u v)) * santaloDens u v (tanB D u) (tanB D v) ∂arcMeasure ∂arcMeasure

def ABf (f : Kern) (D : Pt) : ℝ :=
  ∫ u in arcA D, ∫ v in arcB D,
    cutKern f (arccos (inner ℝ u v)) * santaloDens u v (tanA D u) (tanB D v) ∂arcMeasure ∂arcMeasure

def Rsame (f : Kern) : ℝ := ∫ D in LamC, (AAf f D + BBf f D)

def ABint (f : Kern) : ℝ := ∫ D in LamC, ABf f D

def deltaV (D : Pt) : ℝ := arccos (2 * Rc ‖D‖ ‖D - e‖ ^ 2 - 1)

def Pprim (f : Kern) (d : ℝ) : ℝ := ∫ t in (0 : ℝ)..d, phiK f t

def rhoK : Kern → ℝ → ℝ
  | .one, x => (1 - 2 * x) / (1 - x ^ 2)
  | .cos, x => (1 / 4 - x ^ 2) / (1 - x ^ 2)

def Bf (f : Kern) (D : Pt) : ℝ :=
  ∫ u in arcA D, ∫ v in arcB D,
    (if 1 / 2 < inner ℝ u v then
        rhoK f (inner ℝ u v) * inner ℝ (nAv D) (cross u v) * inner ℝ (nBv D) (cross u v) else 0) /
      (√(1 - ‖D‖ ^ 2 / 4) * √(1 - ‖D - e‖ ^ 2 / 4)) ∂arcMeasure ∂arcMeasure

def Ic (f : Kern) : ℝ :=
  ∫ D in LamC, (if offAxis D ∧ Rc ‖D‖ ‖D - e‖ < 1 then 2 * Pprim f (min (deltaV D) (π / 3)) else 0)

def frakB (f : Kern) : ℝ := ∫ D in LamC, Bf f D

def FA : Set Pt := Metric.sphere 0 1 ∩ Metric.closedBall e 1

def FB : Set Pt := Metric.sphere e 1 ∩ Metric.closedBall 0 1

def NAv (p p' : Pt) : Pt := cross p (p' - p)

def NBv (p p' : Pt) : Pt := cross (p' - e) (p' - p)

def circInt (p p' : Pt) : ℝ :=
  ∫ qv in {qv : Pt | ‖qv‖ = 1 ∧ inner ℝ qv (p' - p) = 0 ∧
      midpoint ℝ p p' + √(1 - dist p p' ^ 2 / 4) • qv ∈ LamC},
    (1 - dist p p' ^ 2 / 4) * inner ℝ qv (NAv p p') * inner ℝ qv (NBv p p') ∂arcMeasure

def e1 : Pt := EuclideanSpace.single 1 1

def e2 : Pt := EuclideanSpace.single 2 1

def Hpoly (X Y s : ℝ) : ℝ := -s ^ 2 + s * X * Y + 2 * s - X ^ 2 * Y - X * Y ^ 2 + 3 * X * Y - 1

def a0 (X Y : ℝ) : ℝ := 1 + X * Y / 2

def b0 (X Y : ℝ) : ℝ := 2 * √(X * (1 - X / 4)) * √(Y * (1 - Y / 4))

def chiPlus (X Y s : ℝ) : ℝ := arccos ((a0 X Y - s) / b0 X Y)

def pRep (X : ℝ) : Pt := √(X * (1 - X / 4)) • e1 + (1 - X / 2) • e

def pRep2 (Y χ : ℝ) : Pt :=
  (√(Y * (1 - Y / 4)) * Real.cos χ) • e1 + (√(Y * (1 - Y / 4)) * Real.sin χ) • e2 + (Y / 2) • e

def Dfull : Set (ℝ × ℝ × ℝ) :=
  {v | 0 < v.1 ∧ v.1 < 1 ∧ 0 < v.2.1 ∧ v.2.1 < 1 ∧ 0 < Hpoly v.1 v.2.1 v.2.2}

def Dnear : Set (ℝ × ℝ × ℝ) := {v | v ∈ Dfull ∧ 0 < v.2.2 ∧ v.2.2 < 1}

def IsAxialRotation (R : Pt ≃ₗᵢ[ℝ] Pt) : Prop :=
  R e = e ∧ LinearMap.det R.toLinearEquiv.toLinearMap = 1

end HardSphereB5.SphericalCrofton
