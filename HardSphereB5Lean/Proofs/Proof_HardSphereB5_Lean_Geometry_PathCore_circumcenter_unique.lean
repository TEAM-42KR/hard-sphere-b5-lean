import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
import Mathlib
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_circumradius_sq
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_tetrahedron_metric
set_option autoImplicit false

noncomputable section
open MeasureTheory Real
private abbrev HardSphereB5.Lean.Geometry.PathCore.s5c_scope_anchor_circumcenter_unique : Unit := ()
section
open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
variable {c : Fin 4 → Pt} {X Y s : ℝ}

private theorem HardSphereB5.Lean.Geometry.PathCore.circumcenter_unique_of_values (hc : IsPathConfig c X Y s)
    (h1 : ∃ O : Pt, ∀ i, dist O (c i) ^ 2 = 1 - P4poly X Y s / (4 * Hpoly X Y s))
    (h2 : 0 < s ∧ s < 3 ∧ AffineIndependent ℝ c ∧
      (∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < Deltaf c i j k) ∧
      (det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)) ^ 2 = Hpoly X Y s / 4) :
    ∃! O : Pt, ∀ i, dist O (c i) ^ 2 = 1 - P4poly X Y s / (4 * Hpoly X Y s) := by
  classical
  let sx : Affine.Simplex ℝ Pt 3 := ⟨c, h2.2.2.1⟩
  have hspan : affineSpan ℝ (Set.range c) = ⊤ :=
    h2.2.2.1.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [HardSphereB5.Lean.Pt])
  have hcenter (p : Pt)
      (hp : ∀ i, dist p (c i) ^ 2 = 1 - P4poly X Y s / (4 * Hpoly X Y s)) :
      p = sx.circumcenter := by
    apply sx.eq_circumcenter_of_dist_eq (r := dist p (c 0))
    · simpa only [sx, hspan, AffineSubspace.mem_top]
    · intro i
      change dist (c i) p = dist p (c 0)
      rw [dist_comm]
      exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ((hp i).trans (hp 0).symm)
  obtain ⟨O, hO⟩ := h1
  refine ⟨O, hO, ?_⟩
  intro p hp
  exact (hcenter p hp).trans (hcenter O hO).symm

private theorem HardSphereB5.Lean.Geometry.PathCore.circumcenter_unique_of_deps
(hRadius : ∀ {c : Fin 4 → Pt} {X Y s : ℝ}, ∀ (hc : IsPathConfig c X Y s),
∃ O : Pt, ∀ i, dist O (c i) ^ 2 = 1 - P4poly X Y s / (4 * Hpoly X Y s))
(hMetric : ∀ {c : Fin 4 → Pt} {X Y s : ℝ}, ∀ (hc : IsPathConfig c X Y s),
0 < s ∧ s < 3 ∧ AffineIndependent ℝ c ∧
  (∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < Deltaf c i j k) ∧
  (det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)) ^ 2 = Hpoly X Y s / 4)
(hc : IsPathConfig c X Y s) :
∃! O : Pt, ∀ i, dist O (c i) ^ 2 = 1 - P4poly X Y s / (4*Hpoly X Y s) := by
  exact circumcenter_unique_of_values hc (hRadius hc) (hMetric hc)

end

open HardSphereB5.Lean.Geometry.PathCore
open HardSphereB5.Lean (Pt)
open scoped Classical RealInnerProductSpace
variable {c : Fin 4 → Pt} {X Y s : ℝ}
theorem proof_HardSphereB5_Lean_Geometry_PathCore_circumcenter_unique (hc : IsPathConfig c X Y s) :
  ∃! O : Pt, ∀ i, dist O (c i) ^ 2 = 1 - P4poly X Y s / (4*Hpoly X Y s) := by
  exact circumcenter_unique_of_deps circumradius_sq tetrahedron_metric hc
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_circumcenter_unique
