import HardSphereB5Lean.Proofs.Proof_Gnomonic_disk_graph_measure_of_weighted_projection
import HardSphereB5Lean.Definitions.Def_Gnomonic_unitDisk
set_option autoImplicit false
open MeasureTheory SphereGeom Gnomonic

theorem Gnomonic.disk_graph_measure_of_weighted_projection :
    ∀ (hprojection :
      Measure.map planeProjection
        ((dOmega.restrict {u : E3 | 0 < u 2}).withDensity (fun u => ENNReal.ofReal (u 2))) =
        (volume : Measure (ℝ × ℝ)).restrict unitDisk), Measure.map upperGraph
      (((volume : Measure (ℝ × ℝ)).restrict unitDisk).withDensity graphDensity) =
      dOmega.restrict upperHemisphere :=
  @proof_Gnomonic_disk_graph_measure_of_weighted_projection
