import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom
namespace SolidGeom.ClassicalInputs
abbrev E2 := EuclideanSpace ℝ (Fin 2)
def e0 : E2 := WithLp.toLp 2 ![1,0]
def e1 : E2 := WithLp.toLp 2 ![0,1]
def cross2 (v w : E2) : ℝ := v 0*w 1-v 1*w 0

structure PositiveConvexBoundary where
  n : ℕ
  D : Set E2
  gamma : Fin (n+1) → ℝ → E2
  len : Fin (n+1) → ℝ
  compact : IsCompact D
  convex : Convex ℝ D
  interior_nonempty : (interior D).Nonempty
  len_pos : ∀ j, 0 < len j
  smooth : ∀ j, ContDiff ℝ 2 (gamma j)
  regular : ∀ j, ∀ t ∈ Set.Icc 0 (len j), deriv (gamma j) t ≠ 0
  cyclic : ∀ j, gamma j (len j) = gamma (j+1) 0
  injective : ∀ j, Set.InjOn (gamma j) (Set.Ico 0 (len j))
  disjoint_arcs : ∀ j k, j ≠ k →
    Disjoint (gamma j '' Set.Ioo 0 (len j)) (gamma k '' Set.Ioo 0 (len k))
  boundary : (⋃ j, gamma j '' Set.Icc 0 (len j)) = frontier D
  left : ∀ j, ∀ t ∈ Set.Ioo 0 (len j), ∀ x ∈ D,
    0 ≤ cross2 (deriv (gamma j) t) (x-gamma j t)

def GreenStmt : Prop := ∀ b : PositiveConvexBoundary, ∀ P Q : E2 → ℝ,
  ContDiff ℝ 1 P → ContDiff ℝ 1 Q →
  (∫ y in b.D, (fderiv ℝ Q y) e0 - (fderiv ℝ P y) e1) =
    ∑ j, ∫ t in (0)..(b.len j),
      P (b.gamma j t) * (deriv (b.gamma j) t) 0 +
      Q (b.gamma j t) * (deriv (b.gamma j) t) 1

def turn (v w : E2) : ℝ := Complex.arg ⟨inner ℝ v w, cross2 v w⟩

def HopfUmlaufsatzStmt : Prop := ∀ b : PositiveConvexBoundary,
  (∑ j, ∫ t in (0)..(b.len j),
    cross2 (deriv (b.gamma j) t) (deriv (deriv (b.gamma j)) t) /
      ‖deriv (b.gamma j) t‖^2) +
  (∑ j, turn (deriv (b.gamma j) (b.len j)) (deriv (b.gamma (j+1)) 0)) = 2*π

structure SurfaceCalculusInputs : Prop where
  green : GreenStmt
  hopf : HopfUmlaufsatzStmt
end SolidGeom.ClassicalInputs
end
