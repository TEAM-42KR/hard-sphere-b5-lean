import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Pair_cylinder_frame_orthonormal
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Pair.cylinder_frame_orthonormal :
    ∀ (z φ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1), Orthonormal ℝ ![
      (WithLp.toLp 2 ![-Real.sin φ, Real.cos φ, 0] : E3),
      (WithLp.toLp 2 ![-z * Real.cos φ, -z * Real.sin φ, Real.sqrt (1-z^2)] : E3),
      (WithLp.toLp 2 ![Real.sqrt (1-z^2) * Real.cos φ, Real.sqrt (1-z^2) * Real.sin φ, z] : E3)] :=
  @proof_SphereGeom_Aux_Pair_cylinder_frame_orthonormal
