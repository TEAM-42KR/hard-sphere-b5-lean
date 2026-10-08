import HardSphereB5Lean.Proofs.Proof_ConvexDisk_exists_homeomorph_closedBall
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false

theorem ConvexDisk.exists_homeomorph_closedBall :
    ∀ {s : Set (EuclideanSpace ℝ (Fin 2))} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hint : (interior s).Nonempty), Nonempty (s ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  @proof_ConvexDisk_exists_homeomorph_closedBall
