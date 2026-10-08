import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
namespace HardSphereB5.SphericalCrofton.Aux.Santalo

structure Charts where
  oA : Pt
  oB : Pt
  EA : Fin 2 → Pt
  EB : Fin 2 → Pt
  TA : ℝ
  TB : ℝ

def rA (D : Pt) : ℝ := Real.sqrt (1 - ‖D‖ ^ 2 / 4)
def rB (D : Pt) : ℝ := Real.sqrt (1 - ‖D - e‖ ^ 2 / 4)
def u (D : Pt) (C : Charts) (t : ℝ) : Pt := circlePt C.oA (C.EA 0) (C.EA 1) (rA D) t
def v (D : Pt) (C : Charts) (t : ℝ) : Pt := circlePt C.oB (C.EB 0) (C.EB 1) (rB D) t
def delta (D : Pt) (C : Charts) (t s : ℝ) : ℝ := Real.arccos (inner ℝ (u D C t) (v D C s))
def Q (f : Kern) (D : Pt) (C : Charts) (t s : ℝ) : ℝ := Pprim f (min (delta D C t s) (Real.pi / 3))
def Q2 (f : Kern) (D : Pt) (C : Charts) (t s : ℝ) : ℝ := deriv (Q f D C t) s
def Q12 (f : Kern) (D : Pt) (C : Charts) (t s : ℝ) : ℝ := deriv (fun z => Q2 f D C z s) t

def abKernel (f : Kern) (D : Pt) (p q : Pt) : ℝ :=
  cutKern f (arccos (inner ℝ p q)) * santaloDens p q (tanA D p) (tanB D q)
def bKernel (f : Kern) (D : Pt) (p q : Pt) : ℝ :=
  (if 1 / 2 < inner ℝ p q then rhoK f (inner ℝ p q) *
    inner ℝ (nAv D) (cross p q) * inner ℝ (nBv D) (cross p q) else 0) / (rA D * rB D)
def J (f : Kern) (D : Pt) (C : Charts) (t s : ℝ) : ℝ :=
  rA D * rB D * abKernel f D (u D C t) (v D C s)
def H (f : Kern) (D : Pt) (C : Charts) (t s : ℝ) : ℝ :=
  rA D * rB D * bKernel f D (u D C t) (v D C s)

def IsChart (D : Pt) (C : Charts) : Prop :=
  Orthonormal ℝ C.EA ∧ Orthonormal ℝ C.EB ∧
  0 < rA D ∧ 0 < rB D ∧ 0 < C.TA ∧ 0 < C.TB ∧
  C.TA ≤ 2 * Real.pi ∧ C.TB ≤ 2 * Real.pi ∧
  arcA D = u D C '' Set.Icc 0 C.TA ∧
  arcB D = v D C '' Set.Icc 0 C.TB ∧
  (∀ t, HasDerivAt (u D C) (cross (nAv D) (u D C t)) t) ∧
  (∀ s, HasDerivAt (v D C) (-cross (nBv D) (v D C s)) s)

end HardSphereB5.SphericalCrofton.Aux.Santalo
