import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem proof_ConvexDisk_exists_homeomorph_closedBall {s : Set E}
    (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hint : (interior s).Nonempty) :
    Nonempty (s ≃ₜ Metric.closedBall (0 : E) 1) := by
  obtain ⟨e, _, hclosure, _⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      hconv hint hcomp.isBounded
  have himage : e '' s = Metric.closedBall (0 : E) 1 := by
    simpa only [hcomp.isClosed.closure_eq] using hclosure
  exact ⟨(e.image s).trans (Homeomorph.setCongr himage)⟩
