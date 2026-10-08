import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_MovingArc_rawA
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_normal_cancel_A
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_normal_cancel_B
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Coarea_inner_unit_distance
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
set_option maxHeartbeats 900000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_source_normalization (f : Kern) (D u v : Pt) (hD : D ∈ LamC) (hu : u ∈ arcA D) (hv : v ∈ arcB D) :
  (if 1 / 2 < inner ℝ u v then rhoK f (inner ℝ u v) * inner ℝ (nAv D) (cross u v) * inner ℝ (nBv D) (cross u v) else 0) /
    (HardSphereB5.SphericalCrofton.Aux.MovingArc.rA D * HardSphereB5.SphericalCrofton.Aux.MovingArc.rB D) =
  (if 0 < dist (D+u) (D+v) ∧ dist (D+u) (D+v) < 1 then
    rhoK f (1-dist (D+u) (D+v)^2/2) * inner ℝ u (NAv (D+u) (D+v)) * inner ℝ v (NBv (D+u) (D+v)) /
      (‖D‖ * ‖D-e‖ * HardSphereB5.SphericalCrofton.Aux.MovingArc.rA D * HardSphereB5.SphericalCrofton.Aux.MovingArc.rB D) else 0) := by
  have hD0 : D ≠ 0 := by intro hz; simpa [arcA,hz] using hu
  have hDe : D ≠ e := by intro hz; simpa [arcB,hz] using hv
  have huarc : u ∈ SigmaD D ∧ ‖D+u‖=1 := by simpa only [arcA,if_neg hD0,Set.mem_setOf_eq] using hu
  have hvarc : v ∈ SigmaD D ∧ dist (D+v) e=1 := by simpa only [arcB,if_neg hDe,Set.mem_setOf_eq] using hv
  have huN : ‖u‖=1 := huarc.1.1
  have hvN : ‖v‖=1 := hvarc.1.1
  have ha : ‖D‖≤1 := by simpa [Metric.mem_closedBall,dist_zero_right] using hD.1
  have hb : ‖D-e‖≤1 := by simpa [Metric.mem_closedBall,dist_eq_norm] using hD.2
  have hra : 0 < Aux.MovingArc.rA D := by
    apply Real.sqrt_pos.2
    nlinarith [norm_nonneg D]
  have hrb : 0 < Aux.MovingArc.rB D := by
    apply Real.sqrt_pos.2
    nlinarith [norm_nonneg (D-e)]
  have hna := norm_ne_zero_iff.2 hD0
  have hnb := norm_ne_zero_iff.2 (sub_ne_zero.mpr hDe)
  have hdist : dist (D+u) (D+v)=dist u v := dist_add_left D u v
  have hx : inner ℝ u v=1-dist (D+u) (D+v)^2/2 := by
    rw [hdist]
    exact Aux.Coarea.inner_unit_distance u v huN hvN
  by_cases huv : u=v
  · subst v
    simp [hdist,SphereGeom.cross]
  · have hdpos : 0 < dist (D+u) (D+v) := by rw [hdist]; exact dist_pos.mpr huv
    have hcut : (1/2 : ℝ) < inner ℝ u v ↔
        (0<dist (D+u) (D+v) ∧ dist (D+u) (D+v)<1) := by
      rw [hx]
      constructor
      · intro hh
        exact ⟨hdpos,by nlinarith⟩
      · intro hh
        nlinarith [hh.2]
    by_cases hn : (1/2 : ℝ) < inner ℝ u v
    · rw [if_pos hn,if_pos (hcut.mp hn),← hx,
        ← Aux.Coarea.normal_cancel_A D u v,← Aux.Coarea.normal_cancel_B D u v]
      field_simp [hna,hnb,hra.ne',hrb.ne']
    · rw [if_neg hn,if_neg (fun hh => hn (hcut.mpr hh)),zero_div]
