import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
open Set

theorem proof_HardSphereB5_SphericalCrofton_Aux_Geom_cap_heights_lt_one (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (hint : (sInterior (⋂ m, cap (n m) (h m))).Nonempty) :
    ∀ m, h m < 1 := by
  classical
  have hrank : 1 < Module.rank ℝ Pt := by
    rw [← Module.finrank_eq_rank]
    simp [Pt, finrank_euclideanSpace_fin]
  letI : PreconnectedSpace (Metric.sphere (0 : Pt) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere hrank (0 : Pt) 1)
  let T : Set (Metric.sphere (0 : Pt) 1) :=
    Subtype.val ⁻¹' (⋂ m, cap (n m) (h m))
  obtain ⟨x, y, hy, hxy⟩ := hint
  change y ∈ interior T at hy
  intro m
  by_contra hm
  have hmh : 1 ≤ h m := le_of_not_gt hm
  let ns : Metric.sphere (0 : Pt) 1 := ⟨n m, by
    simpa only [Metric.mem_sphere, dist_zero_right] using hn m⟩
  have hT : T ⊆ {ns} := by
    intro u hu
    have hucap : (u : Pt) ∈ cap (n m) (h m) := mem_iInter.mp hu m
    have huNorm : ‖(u : Pt)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    have hiUpper := real_inner_le_one_of_norm_eq_one (hn m) huNorm
    have hiEq : inner ℝ (n m) (u : Pt) = 1 := le_antisymm hiUpper (le_trans hmh hucap.2)
    have huEq : n m = (u : Pt) :=
      (inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) (hn m) huNorm).mp hiEq
    exact mem_singleton_iff.mpr (Subtype.ext huEq.symm)
  have hyEq : y = ns := mem_singleton_iff.mp (hT (interior_subset hy))
  have hnint : ns ∈ interior T := hyEq ▸ hy
  have hI : interior T = {ns} := by
    apply subset_antisymm
    · exact interior_subset.trans hT
    · intro u hu
      rcases mem_singleton_iff.mp hu with rfl
      exact hnint
  have hopen : IsOpen ({ns} : Set (Metric.sphere (0 : Pt) 1)) := by
    rw [← hI]
    exact isOpen_interior
  have huniv : ({ns} : Set (Metric.sphere (0 : Pt) 1)) = univ :=
    (show IsClopen {ns} from ⟨isClosed_singleton, hopen⟩).eq_univ (singleton_nonempty ns)
  let negns : Metric.sphere (0 : Pt) 1 := ⟨-n m, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_neg, hn m]⟩
  have hnegMem : negns ∈ ({ns} : Set (Metric.sphere (0 : Pt) 1)) := by
    rw [huniv]
    exact mem_univ _
  have hnegEq : -n m = n m := congrArg Subtype.val (mem_singleton_iff.mp hnegMem)
  have hnzero : n m = 0 := by
    ext i
    have hi : -(n m i) = n m i := congrArg (fun v : Pt => v i) hnegEq
    change n m i = 0
    linarith
  have hnorm := hn m
  rw [hnzero, norm_zero] at hnorm
  norm_num at hnorm
