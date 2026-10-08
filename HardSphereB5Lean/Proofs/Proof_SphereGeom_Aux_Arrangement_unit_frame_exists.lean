import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false
open MeasureTheory Real SphereGeom
open HardSphereB5.Lean (Pt)
open scoped Classical

set_option maxHeartbeats 500000

theorem proof_SphereGeom_Aux_Arrangement_unit_frame_exists (n : Pt) (hn : ‖n‖ = 1) :
    ∃ e1 e2 : Pt, Orthonormal ℝ ![e1, e2, n] := by
  let v : Fin 3 → Pt := fun _ => n
  let s : Set (Fin 3) := {2}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    apply orthonormal_subsingleton_iff.mpr
    intro i
    exact hn
  have hcard : Module.finrank ℝ Pt = Fintype.card (Fin 3) := by
    simp [HardSphereB5.Lean.Pt]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  have hb2 : b 2 = n := hb 2 (by simp [s])
  refine ⟨b 0, b 1, ?_⟩
  have hvec : ![b 0, b 1, n] = (b : Fin 3 → Pt) := by
    ext i
    fin_cases i <;> simp [hb2]
  rw [hvec]
  exact b.orthonormal
