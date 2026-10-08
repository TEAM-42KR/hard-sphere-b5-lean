import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_Psi_Phi_arc
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_sourceCenter
set_option autoImplicit false
open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
open HardSphereB5.SphericalCrofton.Aux.MovingArc
theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_Phi_injOn_regular (S : Set Chart5)
    (hS : ∀ x ∈ S, sourceRegular x ∧
      Rc ‖sourceCenter x‖ ‖sourceCenter x-e‖ < 1 ∧
      x 3 ∈ Set.Icc (-(halfA (sourceCenter x))) (halfA (sourceCenter x)) ∧
      x 4 ∈ Set.Icc (-(halfB (sourceCenter x))) (halfB (sourceCenter x))) : Set.InjOn Phi S  := by
  intro x hx y hy hxy
  rcases hS x hx with ⟨hxr,hxR,hxA,hxB⟩
  rcases hS y hy with ⟨hyr,hyR,hyA,hyB⟩
  have hi := HardSphereB5.SphericalCrofton.Aux.Coarea.Psi_Phi_arc x hxr hxR hxA hxB
  have hj := HardSphereB5.SphericalCrofton.Aux.Coarea.Psi_Phi_arc y hyr hyR hyA hyB
  calc x = Psi (Phi x) := hi.symm
       _ = Psi (Phi y) := congrArg Psi hxy
       _ = y := hj
