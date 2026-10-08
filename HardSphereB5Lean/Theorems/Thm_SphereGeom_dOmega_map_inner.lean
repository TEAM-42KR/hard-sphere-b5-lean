import HardSphereB5Lean.Proofs.Proof_SphereGeom_dOmega_map_inner
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.dOmega_map_inner :
    ∀ (n : E3) (hn : ‖n‖ = 1), dOmega.map (fun u => inner ℝ n u) =
      ENNReal.ofReal (2 * Real.pi) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1) :=
  @proof_SphereGeom_dOmega_map_inner
