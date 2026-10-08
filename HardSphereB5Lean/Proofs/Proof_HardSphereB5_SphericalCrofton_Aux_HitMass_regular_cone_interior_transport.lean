import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
open Set

theorem proof_HardSphereB5_SphericalCrofton_Aux_HitMass_regular_cone_interior_transport (K : Set Pt) :
    let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}
    ∀ u : Pt, ‖u‖ = 1 → (u ∈ interior C ↔ u ∈ sInterior K) := by
  classical
  dsimp only
  let C : Set Pt := {v | v = 0 ∨ ‖v‖⁻¹ • v ∈ K}
  let P : Set Pt := {v | v ≠ 0}
  let f : Pt → Pt := fun v => ‖v‖⁻¹ • v
  have hP : IsOpen P := isClosed_singleton.isOpen_compl
  have hfnorm (v : Pt) (hv : v ≠ 0) : ‖f v‖ = 1 := by
    have hvp := norm_pos_iff.mpr hv
    simp [f, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvp), ne_of_gt hvp]
  let T : Set (Metric.sphere (0 : Pt) 1) := Subtype.val ⁻¹' K
  have hsC : ∀ z : Metric.sphere (0 : Pt) 1, (z : Pt) ∈ C ↔ (z : Pt) ∈ K := by
    intro z
    have hznorm : ‖(z : Pt)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using z.property
    have hz0 : (z : Pt) ≠ 0 := by intro hh; simp [hh] at hznorm
    simp [C, hznorm, hz0]
  intro u hu
  have hu0 : u ≠ 0 := by intro hh; simp [hh] at hu
  let us : Metric.sphere (0 : Pt) 1 := ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu⟩
  constructor
  · intro huC
    have hO : IsOpen ((Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' interior C) :=
      isOpen_interior.preimage continuous_subtype_val
    have hOT : (Subtype.val : Metric.sphere (0 : Pt) 1 → Pt) ⁻¹' interior C ⊆ T := by
      intro z hz
      exact (hsC z).mp (interior_subset hz)
    refine ⟨us, interior_mono hOT ?_, rfl⟩
    rw [hO.interior_eq]
    exact huC
  · rintro ⟨z, hz, hzu⟩
    have hNmap : Continuous (fun v : P => f (v : Pt)) :=
      (continuous_subtype_val.norm.inv₀ (fun v => norm_ne_zero_iff.mpr v.property)).smul continuous_subtype_val
    let fs : P → Metric.sphere (0 : Pt) 1 := fun v =>
      ⟨f v, by simpa [Metric.mem_sphere, dist_zero_right] using hfnorm v v.property⟩
    have hfs : Continuous fs := hNmap.subtype_mk _
    let up : P := ⟨u, hu0⟩
    have hfup : fs up = z := by
      apply Subtype.ext
      change f u = (z : Pt)
      simp [f, hu, hzu]
    let W := fs ⁻¹' interior T
    have hW : IsOpen W := hfs.isOpen_preimage _ isOpen_interior
    have huW : up ∈ W := by change fs up ∈ interior T; rw [hfup]; exact hz
    have hO : IsOpen ((Subtype.val : P → Pt) '' W) := hP.isOpenMap_subtype_val _ hW
    have hOC : ((Subtype.val : P → Pt) '' W) ⊆ C := by
      rintro v ⟨vp, hvp, rfl⟩
      have hvpre : fs vp ∈ T := interior_subset hvp
      exact Or.inr hvpre
    apply interior_mono hOC
    rw [hO.interior_eq]
    exact ⟨up, huW, rfl⟩
