import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section
theorem proof_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_section_nonantipodal_joined {K : Set Pt} (hK : IsRegularRegionCrofton K) (p : Pt) {u v : Pt}
    (hu : u ∈ greatCircle p ∩ K) (hv : v ∈ greatCircle p ∩ K)
    (huv : u ≠ -v) : JoinedIn (greatCircle p ∩ K) u v := by
  let z : ℝ → Pt := fun t => (1 - t) • u + t • v
  have hun : ‖u‖ = 1 := hu.1.1
  have hvn : ‖v‖ = 1 := hv.1.1
  have hzn (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : z t ≠ 0 := by
    intro hz
    have heq : (1 - t) • u = -(t • v) := eq_neg_of_add_eq_zero_left hz
    have hn := congrArg norm heq
    simp only [norm_smul, norm_neg, Real.norm_eq_abs, hun, hvn, mul_one,
      abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr ht.2)] at hn
    have ht2 : t = (1 / 2 : ℝ) := by linarith
    have hzero : (1 / 2 : ℝ) • (u + v) = 0 := by
      norm_num [z, ht2, smul_add] at hz ⊢
      exact hz
    have huv0 : u + v = 0 := (smul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact huv (eq_neg_of_add_eq_zero_left huv0)
  let g : ℝ → Pt := fun t => ‖z t‖⁻¹ • z t
  have hzcont : Continuous z := by fun_prop
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    exact (hzcont.norm.continuousOn.inv₀ (fun t ht => norm_ne_zero_iff.mpr (hzn t ht))).smul
      hzcont.continuousOn
  refine JoinedIn.ofLine hgcont ?_ ?_ ?_
  · simp [g, z, hun]
  · simp [g, z, hvn]
  · rintro x ⟨t, ht, rfl⟩
    have hk := hK.geodesically_convex u hu.2 v hv.2 huv t ht
    refine ⟨⟨?_, ?_⟩, hk⟩
    · simpa only [Metric.mem_sphere, dist_zero_right, g, z] using hK.subset_sphere hk
    · simp [g, z, inner_smul_right, inner_add_right, hu.1.2, hv.1.2]
