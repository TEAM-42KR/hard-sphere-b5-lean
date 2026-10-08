import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Coarea_targetRegular
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_target_rectangle_pointwise
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_chart5_ae_linear_ne
set_option autoImplicit false

open MeasureTheory SphereGeom HardSphereB5.SphericalCrofton HardSphereB5.SphericalCrofton.Aux.Coarea
open HardSphereB5.Lean (Pt e)
set_option maxHeartbeats 1000000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_target_regular_ae :
    ∀ᵐ y : Chart5 ∂volume,
      (y 0 ∈ Set.Icc (1/2 : ℝ) 1 ∧ y 2 ∈ Set.Icc (-1 : ℝ) (-1/2) ∧
        y 1 ∈ Set.Icc (-Real.pi) Real.pi ∧ y 3 ∈ Set.Icc (-Real.pi) Real.pi ∧
        y 4 ∈ Set.Icc (-Real.pi) Real.pi ∧
        0 < dist (targetEndpointA y) (targetEndpointB y) ∧
        dist (targetEndpointA y) (targetEndpointB y) < 1 ∧ targetCenter y ∈ LamC) →
      targetRegular y := by
  have heval (i : Fin 5) (c : ℝ) : ∀ᵐ y : Chart5 ∂volume, y i ≠ c := by
    let L : Chart5 →ₗ[ℝ] ℝ := EuclideanSpace.projₗ i
    have hL : L ≠ 0 := by
      intro h
      have hh := congrArg (fun f : Chart5 →ₗ[ℝ] ℝ => f (EuclideanSpace.single i (1 : ℝ))) h
      norm_num [L,EuclideanSpace.projₗ,PiLp.projₗ] at hh
    exact chart5_ae_linear_ne L hL c
  have hdiag : ∀ᵐ y : Chart5 ∂volume, y 1 ≠ y 3 := by
    let L : Chart5 →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1 - EuclideanSpace.projₗ 3
    have hL : L ≠ 0 := by
      intro h
      have hh := congrArg (fun f : Chart5 →ₗ[ℝ] ℝ => f (EuclideanSpace.single (1 : Fin 5) (1 : ℝ))) h
      norm_num [L,EuclideanSpace.projₗ,PiLp.projₗ,show (3 : Fin 5) ≠ 1 by decide] at hh
    have h := chart5_ae_linear_ne L hL 0
    change ∀ᵐ y : Chart5 ∂volume, y 1-y 3 ≠ 0 at h
    simpa only [sub_ne_zero] using h
  filter_upwards [heval 0 (1/2),heval 0 1,heval 2 (-1),heval 2 (-1/2),
    heval 1 (-Real.pi),heval 1 Real.pi,heval 3 (-Real.pi),heval 3 Real.pi,
    heval 4 (-Real.pi),heval 4 Real.pi,hdiag] with
    y hy00 hy01 hy20 hy21 hy10 hy11 hy30 hy31 hy40 hy41 hy13
  rintro ⟨h0,h2,h1,h3,h4,hz0,hz1,hD⟩
  exact target_rectangle_pointwise y
    ⟨lt_of_le_of_ne h0.1 hy00.symm,lt_of_le_of_ne h0.2 hy01⟩
    ⟨lt_of_le_of_ne h2.1 hy20.symm,lt_of_le_of_ne h2.2 hy21⟩
    ⟨lt_of_le_of_ne h1.1 hy10.symm,lt_of_le_of_ne h1.2 hy11⟩
    ⟨lt_of_le_of_ne h3.1 hy30.symm,lt_of_le_of_ne h3.2 hy31⟩
    ⟨lt_of_le_of_ne h4.1 hy40.symm,lt_of_le_of_ne h4.2 hy41⟩
    hy13 hz0 hz1 hD
