import HardSphereB5Lean.Definitions.Def_SolidGeom_CapPolar_BulkMatching
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom SolidGeom.CapPolar
open HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
open scoped RealInnerProductSpace
set_option maxHeartbeats 1200000
private lemma SolidGeom.CapPolar.caps_measurable (P : Profile) : MeasurableSet (SolidGeom.CapPolar.caps P) := by
  have hc : IsClosed (SolidGeom.CapPolar.caps P) := by
    have he : SolidGeom.CapPolar.caps P = {u : E3 | ‖u‖=1} ∩ ⋂ j, {u | P.height j ≤ inner ℝ (P.normal j) u} := by
      ext u
      simp [SolidGeom.CapPolar.caps]
    rw [he]
    exact (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop))
  exact hc.measurableSet

private lemma SolidGeom.CapPolar.matching_dist_pos {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (j : Fin 3) : 0 < dist (c i) (c (o j)) := by
  have hh := P.height_pos j
  rw [hm.height_eq j] at hh
  linarith

private lemma SolidGeom.CapPolar.matching_labels {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (m : Fin 4) : m=i ∨ ∃ j : Fin 3, m=o j := by
  have hcover : ∀ i a b d m : Fin 4, a ≠ i → b ≠ i → d ≠ i → a ≠ b → a ≠ d → b ≠ d →
      m=i ∨ m=a ∨ m=b ∨ m=d := by decide
  have hc := hcover i (o 0) (o 1) (o 2) m (hm.label_ne 0) (hm.label_ne 1) (hm.label_ne 2)
    (fun h => (by decide : (0:Fin 3) ≠ 1) (hm.label_injective h))
    (fun h => (by decide : (0:Fin 3) ≠ 2) (hm.label_injective h))
    (fun h => (by decide : (1:Fin 3) ≠ 2) (hm.label_injective h))
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨0,h⟩
  · exact Or.inr ⟨1,h⟩
  · exact Or.inr ⟨2,h⟩

private lemma SolidGeom.CapPolar.matching_inner_ball {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (j : Fin 3) (u : E3) (hu : ‖u‖=1) :
    P.height j ≤ inner ℝ (P.normal j) u ↔ c i+u ∈ Metric.closedBall (c (o j)) 1 := by
  let d := dist (c i) (c (o j))
  let v := c (o j)-c i
  have hd := matching_dist_pos hm j
  have hn : ‖v‖^2=d^2 := by dsimp [v,d];rw [← dist_eq_norm,dist_comm]
  have hv : c i+u-c (o j) = u-v := by dsimp [v];abel
  have hsq : dist (c i+u) (c (o j))^2 = 1-2*inner ℝ v u+d^2 := by
    rw [dist_eq_norm,hv,norm_sub_sq_real,hu,hn]
    rw [real_inner_comm]
    ring
  rw [hm.height_eq j,hm.normal_eq j,real_inner_smul_left]
  change d/2 ≤ d⁻¹*inner ℝ v u ↔ dist (c i+u) (c (o j)) ≤ 1
  have he : d/2 ≤ d⁻¹*inner ℝ v u ↔ d^2/2 ≤ inner ℝ v u := by
    rw [show d⁻¹*inner ℝ v u = inner ℝ v u/d by ring,le_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  rw [he]
  constructor <;> intro h <;> nlinarith [dist_nonneg (x:=c i+u) (y:=c (o j))]

private lemma SolidGeom.CapPolar.matching_inner_sphere {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (j : Fin 3) (u : E3) (hu : ‖u‖=1) :
    P.height j = inner ℝ (P.normal j) u ↔ dist (c i+u) (c (o j))=1 := by
  let d := dist (c i) (c (o j))
  let v := c (o j)-c i
  have hd := matching_dist_pos hm j
  have hn : ‖v‖^2=d^2 := by dsimp [v,d];rw [← dist_eq_norm,dist_comm]
  have hv : c i+u-c (o j) = u-v := by dsimp [v];abel
  have hsq : dist (c i+u) (c (o j))^2 = 1-2*inner ℝ v u+d^2 := by
    rw [dist_eq_norm,hv,norm_sub_sq_real,hu,hn]
    rw [real_inner_comm]
    ring
  rw [hm.height_eq j,hm.normal_eq j,real_inner_smul_left]
  change d/2 = d⁻¹*inner ℝ v u ↔ dist (c i+u) (c (o j)) = 1
  have he : d/2 = d⁻¹*inner ℝ v u ↔ d^2/2 = inner ℝ v u := by
    rw [show d⁻¹*inner ℝ v u = inner ℝ v u/d by ring,eq_div_iff (ne_of_gt hd)]
    constructor <;> intro h <;> nlinarith
  rw [he]
  constructor <;> intro h <;> nlinarith [dist_nonneg (x:=c i+u) (y:=c (o j))]

private lemma SolidGeom.CapPolar.matching_patch_iff {P : Profile} {c : Fin 4 → E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : BulkMatching P c i o) (u : E3) : u ∈ caps P ↔ c i+u ∈ patch c i := by
  constructor
  · rintro ⟨hu,hcaps⟩
    constructor
    · simpa only [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_left] using hu
    · simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left]
      intro m
      rcases matching_labels hm m with hmi | ⟨j,hmj⟩
      · rw [hmi]
        change dist (c i+u) (c i) ≤ 1
        simpa only [dist_eq_norm,add_sub_cancel_left,hu] using (le_rfl : (1:ℝ) ≤ 1)
      · rw [hmj]
        exact (matching_inner_ball hm j u hu).mp (hcaps j)
  · rintro ⟨hsi,hK⟩
    have hu : ‖u‖=1 := by simpa only [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_left] using hsi
    refine ⟨hu,?_⟩
    intro j
    apply (matching_inner_ball hm j u hu).mpr
    simp only [Kset,body,Set.mem_iInter,Finset.mem_univ,forall_true_left] at hK
    exact hK _
theorem proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_profile_patch_measure
    {P : SolidGeom.CapPolar.Profile} {c : Fin 4 → SphereGeom.E3} {i : Fin 4} {o : Fin 3 → Fin 4}
    (hm : SolidGeom.CapPolar.BulkMatching P c i o) :
    HardSphereB5.Lean.Geometry.PathCore.pArea c i Finset.univ=(SphereGeom.dOmega (SolidGeom.CapPolar.caps P)).toReal ∧
      HardSphereB5.Lean.Geometry.PathCore.pMoment c i Finset.univ=
        ∫ u in SolidGeom.CapPolar.caps P, u ∂SphereGeom.dOmega  := by
  let μ : Measure (Metric.sphere (0 : E3) 1) := (volume : Measure E3).toSphere
  let f : Metric.sphere (0 : E3) 1 → E3 := fun u => c i+(u : E3)
  let g : Metric.sphere (0 : E3) 1 → E3 := fun u => (0 : E3)+(u : E3)
  have hf : Measurable f := measurable_const.add measurable_subtype_coe
  have hg : Measurable g := measurable_const.add measurable_subtype_coe
  have hclosed : IsClosed (body c Finset.univ) := by
    unfold body
    exact isClosed_iInter fun j => isClosed_iInter fun _ => Metric.isClosed_closedBall
  have hbody : MeasurableSet (body c Finset.univ) := hclosed.measurableSet
  have hcaps : MeasurableSet (caps P) := caps_measurable P
  have hs : f ⁻¹' body c Finset.univ=g ⁻¹' caps P := by
    ext u
    have hunit : ‖(u : E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using u.property
    have hspi : c i+(u : E3) ∈ Metric.sphere (c i) 1 := by
      simpa only [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_left] using hunit
    have hmemb := (matching_patch_iff hm (u : E3)).symm
    simpa only [Set.mem_preimage,f,g,zero_add,patch,Set.mem_inter_iff,hspi,true_and,Kset] using hmemb
  constructor
  · rw [pArea,if_pos (Finset.mem_univ i)]
    change ((Measure.map f μ) (body c Finset.univ)).toReal=((Measure.map g μ) (caps P)).toReal
    rw [Measure.map_apply hf hbody,Measure.map_apply hg hcaps,hs]
  · rw [pMoment,if_pos (Finset.mem_univ i)]
    change (∫ x in body c Finset.univ, x-c i ∂Measure.map f μ)=
      (∫ x in caps P, x ∂Measure.map g μ)
    have hfsub : AEStronglyMeasurable (fun x : E3 => x-c i) (Measure.map f μ) :=
      (continuous_id.sub (continuous_const : Continuous (fun _ : E3 => c i))).aestronglyMeasurable
    have hfid : AEStronglyMeasurable (fun x : E3 => x) (Measure.map g μ) := continuous_id.aestronglyMeasurable
    rw [setIntegral_map hbody hfsub hf.aemeasurable,setIntegral_map hcaps hfid hg.aemeasurable,hs]
    simp only [f,g,zero_add,add_sub_cancel_left]
#print axioms proof_HardSphereB5_Lean_Geometry_PathCore_Bridge_profile_patch_measure
