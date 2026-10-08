import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_radial_frame_det
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false
open MeasureTheory SphereGeom

theorem SphereGeom.Aux.Crofton.radial_frame_det :
    ∀ (a b g ap bp gp : E3) (r θ : ℝ) (hab : cross a b = g) (ha : inner ℝ ap g = -inner ℝ a gp) (hb : inner ℝ bp g = -inner ℝ b gp), Matrix.det (fun i j : Fin 3 => (![r • (Real.cos θ • ap + Real.sin θ • bp), r • (-Real.sin θ • a + Real.cos θ • b), Real.cos θ • a + Real.sin θ • b] : Fin 3 → E3) j i) = r ^ 2 * inner ℝ (Real.cos θ • a + Real.sin θ • b) gp :=
  @proof_SphereGeom_Aux_Crofton_radial_frame_det
