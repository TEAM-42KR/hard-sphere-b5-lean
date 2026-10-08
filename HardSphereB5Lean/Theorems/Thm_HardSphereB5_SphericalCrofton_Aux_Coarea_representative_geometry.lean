import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_representative_geometry
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.representative_geometry :
    ∀ (v : ℝ × ℝ × ℝ) (hv : v ∈ Dfull), pRep v.1 ∈ FA ∧ pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2) ∈ FB ∧
  0 < v.2.2 ∧ dist (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) = √v.2.2 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_representative_geometry
