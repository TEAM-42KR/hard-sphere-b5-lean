import Mathlib
set_option autoImplicit false

noncomputable section
open MeasureTheory Real

namespace HardSphereB5.Lean

abbrev Pt := EuclideanSpace ℝ (Fin 3)

def D (x : Pt) : Set Pt := Metric.ball x 1

def e : Pt := EuclideanSpace.single 0 1

def lens (l : ℝ) : Set Pt := D 0 ∩ D (l • e)

def lensVol (l : ℝ) : ℝ := (volume (lens l)).toReal

def N (l : ℝ) (o : Pt) : ℝ := (volume (lens l ∩ D o)).toReal

def P (l : ℝ) : ℝ := ∫ o in lens l, N l o ^ 2

def M (l : ℝ) : ℝ := ∫ o in lens l, N l o

def farTriples (l : ℝ) : Set (Fin 3 → Pt) :=
  {x | (∀ i, x i ∈ lens l) ∧ ∀ i j, i ≠ j → 1 ≤ dist (x i) (x j)}

def T (l : ℝ) : ℝ := (volume (farTriples l)).toReal

def nearTriples (l : ℝ) : Set (Fin 3 → Pt) :=
  {x | (∀ i, x i ∈ lens l) ∧ ∀ i j, i ≠ j → dist (x i) (x j) < 1}

def S (l : ℝ) : ℝ := (volume (nearTriples l)).toReal

def Phi (κ : ℝ) : ℝ :=
  4 * π * ∫ l in (0 : ℝ)..2, (1 + κ * (if 1 < l then 1 else 0)) * l ^ 2 * P l

def calT3 : ℝ := 4 * π * ∫ l in (1 : ℝ)..2, l ^ 2 * T l

def mayerF (r : ℝ) : ℝ := if r < 1 then -1 else 0

def IsBiconnected {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.Connected ∧ ∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).Connected

open Classical in
def mayerWeight {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Pt) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j ∧ G.Adj i j then mayerF (dist (x i) (x j)) else 1

open Classical in
def virialB (n : ℕ) : ℝ :=
  -((n : ℝ) / ((n + 1).factorial : ℝ)) *
    ∫ y : Fin n → Pt,
      ∑ G ∈ (Finset.univ.filter fun G : SimpleGraph (Fin (n + 1)) => IsBiconnected G),
        mayerWeight G (Fin.cons (0 : Pt) y : Fin (n + 1) → Pt)

def b5 : ℝ := virialB 4 / virialB 1 ^ 4

open Classical in
def overlapDiagram {n : ℕ} (H : SimpleGraph (Fin (n + 1))) : ℝ :=
  ∫ y : Fin n → Pt,
    ∏ i : Fin (n + 1), ∏ j : Fin (n + 1),
      if i < j ∧ H.Adj i j then
        (if dist ((Fin.cons (0 : Pt) y : Fin (n + 1) → Pt) i)
              ((Fin.cons (0 : Pt) y : Fin (n + 1) → Pt) j) < 1 then (1 : ℝ) else 0)
      else 1

def gK5 : SimpleGraph (Fin 5) := ⊤

def gY9 : SimpleGraph (Fin 5) := (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(2, 3)}

def gW8 : SimpleGraph (Fin 5) := (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(0, 1), s(2, 3)}

def gZ8 : SimpleGraph (Fin 5) := (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(2, 3), s(3, 4)}

def gX7 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 2), s(1, 3)}

def gK23 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(1, 4)}

def gK113 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(1, 4)}

def W8 : ℝ := overlapDiagram gW8
def Y9 : ℝ := overlapDiagram gY9
def K5 : ℝ := overlapDiagram gK5
def Z8 : ℝ := overlapDiagram gZ8
def X7 : ℝ := overlapDiagram gX7
def K23 : ℝ := overlapDiagram gK23
def K113 : ℝ := overlapDiagram gK113

end HardSphereB5.Lean
