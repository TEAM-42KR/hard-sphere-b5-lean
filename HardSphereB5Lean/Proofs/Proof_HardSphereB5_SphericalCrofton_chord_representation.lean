import Mathlib
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_density_measurable
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_Ff_eq_toReal_lintegral
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Interval_frame_fiber_ae
import HardSphereB5Lean.Theorems.Thm_HardSphereB5_SphericalCrofton_Aux_Chord_Pair_gcIntegral_eq_toReal_lintegral
import HardSphereB5Lean.Theorems.Thm_SphereGeom_lintegral_pair_greatCircle
import HardSphereB5Lean.Theorems.Thm_SphereGeom_exists_measurable_frame
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
theorem proof_HardSphereB5_SphericalCrofton_chord_representation {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern) :
    Ff f K = gcIntegral (fun G => if 0 < chordLen K G then kK f (chordLen K G) else 0) := by
  let g : Pt → Pt → ENNReal := (fun u v : Pt => if u ∈ K ∧ v ∈ K ∧ (1 / 2 : ℝ) ≤ inner ℝ u v then ENNReal.ofReal (wK f (inner ℝ u v)) else 0)
  obtain ⟨F₁, F₂, hF₁, hF₂, hF⟩ := SphereGeom.exists_measurable_frame
  have hg : Measurable (Function.uncurry g) :=
    HardSphereB5.SphericalCrofton.Aux.Chord.Pair.density_measurable K hK.isCompact.measurableSet f
  have hp := SphereGeom.lintegral_pair_greatCircle F₁ F₂ hF₁ hF₂ hF g hg
  have he := HardSphereB5.SphericalCrofton.Aux.Chord.Interval.frame_fiber_ae hK f F₁ F₂ hF₁ hF₂ hF
  have hl := lintegral_congr_ae he
  rw [HardSphereB5.SphericalCrofton.Aux.Chord.Pair.Ff_eq_toReal_lintegral hK f,
      HardSphereB5.SphericalCrofton.Aux.Chord.Pair.gcIntegral_eq_toReal_lintegral hK f]
  change (∫⁻ u, ∫⁻ v, g u v ∂dOmega ∂dOmega).toReal = _
  rw [hp]
  congr 2
