import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
set_option autoImplicit false

set_option maxHeartbeats 800000

theorem proof_SphereGeom_Aux_Crofton_angle_unique_Ioc (a b g x : SphereGeom.E3)
    (hframe : Orthonormal ℝ ![a, b, g])
    (hcross : SphereGeom.cross a b = g)
    (hx : x ≠ 0) (hxg : inner ℝ x g = 0) :
    ∃! ψ : ℝ, ψ ∈ Set.Ioc 0 (2 * Real.pi) ∧
      x = ‖x‖ • (Real.cos ψ • a + Real.sin ψ • b) := by
  classical
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hspan : Submodule.span ℝ (Set.range ![a, b, g]) = ⊤ :=
    hframe.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [SphereGeom.E3])
  let e : OrthonormalBasis (Fin 3) ℝ SphereGeom.E3 :=
    OrthonormalBasis.mk hframe hspan.ge
  have he0 : e 0 = a := by simp [e]
  have he1 : e 1 = b := by simp [e]
  have he2 : e 2 = g := by simp [e]
  have hgx : inner ℝ g x = 0 := by rw [real_inner_comm]; exact hxg
  have hdecomp : x = inner ℝ a x • a + inner ℝ b x • b := by
    simpa [Fin.sum_univ_three, he0, he1, he2, hgx] using (e.sum_repr' x).symm
  let z : ℂ := ⟨inner ℝ a x, inner ℝ b x⟩
  have hz_norm : ‖z‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg z) (norm_nonneg x)).mp
    rw [Complex.sq_norm, ← e.repr.norm_map x, EuclideanSpace.real_norm_sq_eq]
    simp [z, Complex.normSq_apply, Fin.sum_univ_three,
      OrthonormalBasis.repr_apply_apply, he0, he1, he2, hgx, pow_two]
  obtain ⟨ψ, hψ, hangle⟩ := AddCircle.eq_coe_Ioc ((Complex.arg z : ℝ) : Real.Angle)
  have hcosarg : Real.cos ψ = Real.cos (Complex.arg z) := by
    exact congrArg Real.Angle.cos hangle
  have hsinarg : Real.sin ψ = Real.sin (Complex.arg z) := by
    exact congrArg Real.Angle.sin hangle
  have hcos : ‖x‖ * Real.cos ψ = inner ℝ a x := by
    simpa only [hz_norm, ← hcosarg] using Complex.norm_mul_cos_arg z
  have hsin : ‖x‖ * Real.sin ψ = inner ℝ b x := by
    simpa only [hz_norm, ← hsinarg] using Complex.norm_mul_sin_arg z
  have hparam : x = ‖x‖ • (Real.cos ψ • a + Real.sin ψ • b) := by
    rw [smul_add, smul_smul, smul_smul, hcos, hsin]
    exact hdecomp
  refine ⟨ψ, ⟨hψ, hparam⟩, ?_⟩
  intro φ hφ
  have haa : inner ℝ a a = 1 := by
    simpa using (orthonormal_iff_ite.mp hframe) (0 : Fin 3) 0
  have hab : inner ℝ a b = 0 := by
    simpa using (orthonormal_iff_ite.mp hframe) (0 : Fin 3) 1
  have hba : inner ℝ b a = 0 := by
    simpa using (orthonormal_iff_ite.mp hframe) (1 : Fin 3) 0
  have hbb : inner ℝ b b = 1 := by
    simpa using (orthonormal_iff_ite.mp hframe) (1 : Fin 3) 1
  have hφcos : ‖x‖ * Real.cos φ = inner ℝ a x := by
    simpa only [inner_add_right, inner_smul_right, haa, hab, mul_one, mul_zero, add_zero] using
      (congrArg (fun y : SphereGeom.E3 => inner ℝ a y) hφ.2).symm
  have hφsin : ‖x‖ * Real.sin φ = inner ℝ b x := by
    simpa only [inner_add_right, inner_smul_right, hba, hbb, mul_one, mul_zero, zero_add] using
      (congrArg (fun y : SphereGeom.E3 => inner ℝ b y) hφ.2).symm
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hc : Real.cos φ = Real.cos ψ := mul_left_cancel₀ hn (hφcos.trans hcos.symm)
  have hs : Real.sin φ = Real.sin ψ := mul_left_cancel₀ hn (hφsin.trans hsin.symm)
  have ha : (φ : Real.Angle) = (ψ : Real.Angle) := Real.Angle.cos_sin_inj hc hs
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc
    (p := 2 * Real.pi) (a := 0) (by simpa using hφ.1) (by simpa using hψ)).mp ha
