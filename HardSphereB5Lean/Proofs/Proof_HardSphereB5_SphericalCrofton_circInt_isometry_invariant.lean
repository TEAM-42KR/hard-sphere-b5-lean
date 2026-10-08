import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_circInt_isometry_invariant (p p' : Pt) (R : Pt ≃ₗᵢ[ℝ] Pt) (hR : R e = e) :
    circInt (R p) (R p') = circInt p p' := by
  have hgram (q a b d : Pt) :
      inner ℝ q (cross a d) * inner ℝ q (cross b d) =
        inner ℝ q q * inner ℝ a b * inner ℝ d d +
        inner ℝ q b * inner ℝ a d * inner ℝ d q +
        inner ℝ q d * inner ℝ a q * inner ℝ d b -
        inner ℝ q q * inner ℝ a d * inner ℝ d b -
        inner ℝ q b * inner ℝ a q * inner ℝ d d -
        inner ℝ q d * inner ℝ a b * inner ℝ d q := by
    simp only [SphereGeom.cross, EuclideanSpace.inner_eq_star_dotProduct,
      WithLp.ofLp_toLp, star_trivial, cross_apply, Matrix.vec3_dotProduct]
    dsimp only [Matrix.cons_val]
    ring
  have hprod (q a b d : Pt) :
      inner ℝ (R q) (cross (R a) (R d)) * inner ℝ (R q) (cross (R b) (R d)) =
        inner ℝ q (cross a d) * inner ℝ q (cross b d) := by
    rw [hgram, hgram]
    simp only [R.inner_map_map]
  have hLam (v : Pt) : R v ∈ LamC ↔ v ∈ LamC := by
    have hd : dist (R v) e = dist v e := by simpa only [hR] using R.dist_map v e
    simp only [LamC, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
      R.norm_map, hd]
  let S (a b : Pt) : Set Pt :=
    {q : Pt | ‖q‖ = 1 ∧ inner ℝ q (b - a) = 0 ∧
      midpoint ℝ a b + √(1 - dist a b ^ 2 / 4) • q ∈ LamC}
  let F (a b q : Pt) : ℝ :=
    (1 - dist a b ^ 2 / 4) * inner ℝ q (NAv a b) * inner ℝ q (NBv a b)
  have hmid (q : Pt) :
      midpoint ℝ (R p) (R p') + √(1 - dist (R p) (R p') ^ 2 / 4) • R q =
        R (midpoint ℝ p p' + √(1 - dist p p' ^ 2 / 4) • q) := by
    simp only [midpoint_eq_smul_add, R.map_add, R.map_smul, R.dist_map]
  have hset : R ⁻¹' S (R p) (R p') = S p p' := by
    ext q
    change (‖R q‖ = 1 ∧ inner ℝ (R q) (R p' - R p) = 0 ∧
        midpoint ℝ (R p) (R p') + √(1 - dist (R p) (R p') ^ 2 / 4) • R q ∈ LamC) ↔
      (‖q‖ = 1 ∧ inner ℝ q (p' - p) = 0 ∧
        midpoint ℝ p p' + √(1 - dist p p' ^ 2 / 4) • q ∈ LamC)
    rw [← R.map_sub, R.inner_map_map, R.norm_map, hmid, hLam]
  have hf (q : Pt) : F (R p) (R p') (R q) = F p p' q := by
    dsimp only [F, NAv, NBv]
    have hb : R p' - e = R (p' - e) := by rw [R.map_sub, hR]
    rw [R.dist_map, ← R.map_sub, hb]
    simp only [mul_assoc]
    rw [hprod]
  have hmp : MeasurePreserving (R : Pt → Pt) arcMeasure arcMeasure := by
    simpa only [arcMeasure, LinearIsometryEquiv.coe_toIsometryEquiv] using R.toIsometryEquiv.measurePreserving_hausdorffMeasure 1
  have hemb : MeasurableEmbedding (R : Pt → Pt) :=
    R.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  change (∫ q in S (R p) (R p'), F (R p) (R p') q ∂arcMeasure) =
    ∫ q in S p p', F p p' q ∂arcMeasure
  calc
    (∫ q in S (R p) (R p'), F (R p) (R p') q ∂arcMeasure) =
        ∫ q in R ⁻¹' S (R p) (R p'), F (R p) (R p') (R q) ∂arcMeasure :=
      (hmp.setIntegral_preimage_emb hemb _ _).symm
    _ = ∫ q in S p p', F p p' q ∂arcMeasure := by
      rw [hset]
      exact integral_congr_ae (Filter.Eventually.of_forall hf)

