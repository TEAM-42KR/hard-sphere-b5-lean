import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Theorems.Thm_SphereGeom_Aux_Crofton_angle_unique_Ioc
import Mathlib.Data.Set.Card
set_option autoImplicit false

set_option maxHeartbeats 800000

theorem proof_SphereGeom_Aux_Crofton_encard_Psi_fiber_eq (a b g : ℝ → SphereGeom.E3) (S : Set ℝ)
    (hframe : ∀ s ∈ S, Orthonormal ℝ ![a s, b s, g s] ∧
      SphereGeom.cross (a s) (b s) = g s)
    (x : SphereGeom.E3) (hx : x ≠ 0) (hxn : ‖x‖ < 1) :
    let Ψ : SphereGeom.E3 → SphereGeom.E3 := fun y =>
      y 2 • (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0))
    let D : Set SphereGeom.E3 := {y | y 0 ∈ S ∧
      y 1 ∈ Set.Ioc 0 (2 * Real.pi) ∧ y 2 ∈ Set.Ioo 0 1}
    (D ∩ Ψ ⁻¹' {x}).encard =
      {s : ℝ | s ∈ S ∧ inner ℝ x (g s) = 0}.encard := by
  classical
  let Ψ : SphereGeom.E3 → SphereGeom.E3 := fun y =>
    y 2 • (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0))
  let D : Set SphereGeom.E3 := {y | y 0 ∈ S ∧
    y 1 ∈ Set.Ioc 0 (2 * Real.pi) ∧ y 2 ∈ Set.Ioo 0 1}
  let F : Set SphereGeom.E3 := D ∩ Ψ ⁻¹' {x}
  let T : Set ℝ := {s | s ∈ S ∧ inner ℝ x (g s) = 0}
  change F.encard = T.encard
  have hunit (s : ℝ) (hs : s ∈ S) (θ : ℝ) :
      ‖Real.cos θ • a s + Real.sin θ • b s‖ = 1 := by
    have hon := (hframe s hs).1
    have haa : inner ℝ (a s) (a s) = 1 := by
      simpa using (orthonormal_iff_ite.mp hon) (0 : Fin 3) 0
    have hab : inner ℝ (a s) (b s) = 0 := by
      simpa using (orthonormal_iff_ite.mp hon) (0 : Fin 3) 1
    have hba : inner ℝ (b s) (a s) = 0 := by
      simpa using (orthonormal_iff_ite.mp hon) (1 : Fin 3) 0
    have hbb : inner ℝ (b s) (b s) = 1 := by
      simpa using (orthonormal_iff_ite.mp hon) (1 : Fin 3) 1
    have hsq : ‖Real.cos θ • a s + Real.sin θ • b s‖ ^ 2 = (1 : ℝ) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, haa, hab, hba, hbb,
        mul_one, mul_zero, add_zero, zero_add]
      nlinarith [Real.cos_sq_add_sin_sq θ]
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp hsq
  have hradius (y : SphereGeom.E3) (hy : y ∈ F) : y 2 = ‖x‖ := by
    rcases hy.1 with ⟨hys, hyθ, hyr⟩
    have hyx : Ψ y = x := Set.mem_singleton_iff.mp hy.2
    have hn : ‖x‖ = y 2 := calc
      ‖x‖ = ‖Ψ y‖ := congrArg norm hyx.symm
      _ = ‖y 2‖ * ‖Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0)‖ :=
        norm_smul _ _
      _ = y 2 := by
        rw [hunit (y 0) hys (y 1), Real.norm_eq_abs, abs_of_pos hyr.1, mul_one]
    exact hn.symm
  have hmap : Set.MapsTo (fun y : SphereGeom.E3 => y 0) F T := by
    intro y hy
    refine ⟨hy.1.1, ?_⟩
    have hon := (hframe (y 0) hy.1.1).1
    have hag : inner ℝ (a (y 0)) (g (y 0)) = 0 := by
      simpa using (orthonormal_iff_ite.mp hon) (0 : Fin 3) 2
    have hbg : inner ℝ (b (y 0)) (g (y 0)) = 0 := by
      simpa using (orthonormal_iff_ite.mp hon) (1 : Fin 3) 2
    have hyx : Ψ y = x := Set.mem_singleton_iff.mp hy.2
    rw [← hyx]
    simp only [Ψ, real_inner_smul_left, inner_add_left, hag, hbg,
      mul_zero, add_zero]
  have hinj : Set.InjOn (fun y : SphereGeom.E3 => y 0) F := by
    intro y hy z hz hzero
    obtain ⟨θ, hθ, huniq⟩ :=
      SphereGeom.Aux.Crofton.angle_unique_Ioc
        (a (y 0)) (b (y 0)) (g (y 0)) x
        (hframe (y 0) hy.1.1).1 (hframe (y 0) hy.1.1).2 hx (hmap hy).2
    have hyparam : x = ‖x‖ •
        (Real.cos (y 1) • a (y 0) + Real.sin (y 1) • b (y 0)) := by
      simpa only [Ψ, hradius y hy] using
        (Set.mem_singleton_iff.mp hy.2).symm
    have hzparam : x = ‖x‖ •
        (Real.cos (z 1) • a (y 0) + Real.sin (z 1) • b (y 0)) := by
      simpa only [Ψ, hradius z hz, ← hzero] using
        (Set.mem_singleton_iff.mp hz.2).symm
    have hyθ : y 1 = θ := huniq (y 1) ⟨hy.1.2.1, hyparam⟩
    have hzθ : z 1 = θ := huniq (z 1) ⟨hz.1.2.1, hzparam⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · exact hzero
    · exact hyθ.trans hzθ.symm
    · exact (hradius y hy).trans (hradius z hz).symm
  have hsurj : Set.SurjOn (fun y : SphereGeom.E3 => y 0) F T := by
    intro s hs
    obtain ⟨θ, hθ, huniq⟩ :=
      SphereGeom.Aux.Crofton.angle_unique_Ioc
        (a s) (b s) (g s) x (hframe s hs.1).1 (hframe s hs.1).2 hx hs.2
    refine ⟨WithLp.toLp 2 ![s, θ, ‖x‖], ?_, rfl⟩
    constructor
    · change s ∈ S ∧ θ ∈ Set.Ioc 0 (2 * Real.pi) ∧ ‖x‖ ∈ Set.Ioo 0 1
      exact ⟨hs.1, hθ.1, norm_pos_iff.mpr hx, hxn⟩
    · change ‖x‖ • (Real.cos θ • a s + Real.sin θ • b s) ∈ ({x} : Set SphereGeom.E3)
      exact Set.mem_singleton_iff.mpr hθ.2.symm
  have hbij : Set.BijOn (fun y : SphereGeom.E3 => y 0) F T := ⟨hmap, hinj, hsurj⟩
  calc
    F.encard = ((fun y : SphereGeom.E3 => y 0) '' F).encard := hinj.encard_image.symm
    _ = T.encard := congrArg Set.encard hbij.image_eq
