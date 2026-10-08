import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_normal_form_volume
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_contraction
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open HardSphereB5.Lean (Pt)
noncomputable section
open MeasureTheory Real HardSphereB5.Lean.Geometry.PathCore

private lemma p7_raw_affine_identity (C F A E T R V : ℝ)
    (hV : V = C - F - A + E / 12 - T / 12)
    (hR : R = (E-T) / 2) : V = C-F-A+R/6 := by
  rw [hV,hR]
  ring

private lemma p7_if_div (b : Prop) [Decidable b] (x : ℝ) :
    (if b then x / 12 else 0) = (if b then x else 0) / 12 := by
  by_cases hb : b <;> simp [hb]

theorem proof_HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_volume {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0)
  (D : ∀ e : PairIndex, PairArcDecomposition c e.1.1 e.1.2) :
  vol c Finset.univ = 8*π/3 - (1/3)*∑ l, (nRet c l : ℝ)*sigmaF c l -
    (1/2)*∑ i, ∑ j, (if i<j then g (dist (c i) (c j))*ell c i j else 0) + rawEndpointSum c D / 6 := by
  have hV := HardSphereB5.Lean.Geometry.PathCore.normal_form_volume hc hP
  have hR := raw_endpoint_contraction hc hP D
  rw [p7_if_div (0 < P4poly X Y s)] at hV
  rw [hV,hR]
  ring

#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_volume
