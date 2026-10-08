import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Coarea_ambient_kernel_measurable_bound
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)

theorem HardSphereB5.SphericalCrofton.Aux.Coarea.ambient_kernel_measurable_bound :
    ∀ (f : Kern),
    let G (D p p' : Pt) : ℝ := rhoK f (inner ℝ (p - D) (p' - D)) *
    inner ℝ (p - D) (NAv p p') * inner ℝ (p' - D) (NBv p p')
  Measurable (fun x : Pt × Pt × Pt => G x.1 x.2.1 x.2.2) ∧
    ∀ (D p p' : Pt), D ∈ LamC → p ∈ FA → p' ∈ FB →
      dist D p = 1 → dist D p' = 1 → 0 < dist p p' → dist p p' < 1 →
      |G D p p'| ≤ 1 :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Coarea_ambient_kernel_measurable_bound
