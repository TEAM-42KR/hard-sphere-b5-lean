import HardSphereB5Lean.Proofs.Proof_SphereGeom_dOmega_compl_sphere
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.dOmega_compl_sphere :
    dOmega (Metric.sphere (0 : E3) 1)ᶜ = 0 :=
  @proof_SphereGeom_dOmega_compl_sphere
