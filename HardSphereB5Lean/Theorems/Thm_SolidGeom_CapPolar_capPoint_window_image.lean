import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_capPoint_window_image
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_BulkMatching
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_wrapWindow
set_option autoImplicit false
noncomputable section

theorem SolidGeom.CapPolar.capPoint_window_image :
    ∀ (P : SolidGeom.CapPolar.Profile) (j : Fin 3) (q : ℝ → ℝ)
    (hq : Continuous q) (hmono : StrictMono q) (L : ℝ) (hL : 0<L), SolidGeom.CapPolar.wrapWindow (2*Real.pi) (q 0) (q L) =
      Set.Ioo 0 (2*Real.pi) ∩ {φ | SolidGeom.CapPolar.polar P.e (P.rho j φ) φ ∈
        (fun t => SolidGeom.CapPolar.polar P.e (P.rho j (q t)) (q t)) '' Set.Ioo 0 L} :=
  @proof_SolidGeom_CapPolar_capPoint_window_image
