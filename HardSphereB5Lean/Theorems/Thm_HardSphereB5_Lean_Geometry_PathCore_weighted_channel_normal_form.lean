import HardSphereB5Lean.Proofs.Proof_HardSphereB5_Lean_Geometry_PathCore_weighted_channel_normal_form
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_Geometry_PathCore_definitionLayer
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5.Lean.Geometry.PathCore.weighted_channel_normal_form :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0) (h ε : ℝ)
  (hchannel : (h=channelH2 Y ∧ ε= -1) ∨ (h=channelH3 X Y s ∧ ε=1)), channelDensity c X h ε = 4*π*hcWeight X*h -
    (∑ i, ∑ j, (if i<j then channelArcCoeff c X h ε i j * ell c i j else 0)) +
    channelCorner c X h + channelEndpoint c X Y s h ε :=
  @proof_HardSphereB5_Lean_Geometry_PathCore_weighted_channel_normal_form
