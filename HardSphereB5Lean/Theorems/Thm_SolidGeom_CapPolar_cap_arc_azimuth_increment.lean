import HardSphereB5Lean.Proofs.Proof_SolidGeom_CapPolar_cap_arc_azimuth_increment
import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_capAxis
set_option autoImplicit false
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
noncomputable section

theorem SolidGeom.CapPolar.cap_arc_azimuth_increment :
    ∀ (p a b e f g : SphereGeom.E3) (A h L : ℝ) (q : ℝ → ℝ) (O : Set ℝ)
    (hh : 0<h) (hA : h<A) (hA1 : A≤1) (hL : 0<L)
    (hpole : Orthonormal ℝ (fun k : Fin 3 => ![p,a,b] k))
    (hb : SphereGeom.cross p a=b) (he : e=SolidGeom.CapPolar.capAxis p a A)
    (hcap : Orthonormal ℝ (fun k : Fin 3 => ![e,f,g] k))
    (hg : SphereGeom.cross e f=g) (hO : IsOpen O) (hI : Set.Icc 0 L ⊆ O)
    (hq : DifferentiableOn ℝ q O)
    (hcurve : Set.EqOn (fun t => SolidGeom.CapPolar.capExitPoint p a b A h (q t))
      (fun t => h • e+Real.sqrt (1-h^2) • (Real.cos t • f+Real.sin t • g)) O), SolidGeom.CapPolar.momentAzimuth A h (q L)-SolidGeom.CapPolar.momentAzimuth A h (q 0)=L :=
  @proof_SolidGeom_CapPolar_cap_arc_azimuth_increment
