import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_cap_circle_polar_chart_ordered
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
set_option autoImplicit false
noncomputable section

theorem SolidGeom.CapPolar.cap_circle_polar_chart_ordered :
    ∀ (p a b e f g : SphereGeom.E3) (A h : ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1)
    (hpole : Orthonormal ℝ (fun k : Fin 3 => ![p,a,b] k))
    (hb : SphereGeom.cross p a=b) (he : e=SolidGeom.CapPolar.capAxis p a A)
    (hcap : Orthonormal ℝ (fun k : Fin 3 => ![e,f,g] k))
    (hg : SphereGeom.cross e f=g), ∃ q : ℝ → ℝ, Differentiable ℝ q ∧ StrictMono q ∧
      (∀ t, q (t+2*Real.pi)=q t+2*Real.pi) ∧ ∀ t,
      SolidGeom.CapPolar.capExitPoint p a b A h (q t)=
        h • e+Real.sqrt (1-h^2) • (Real.cos t • f+Real.sin t • g) :=
  @proof_SolidGeom_CapPolar_cap_circle_polar_chart_ordered
