import HardSphereB5Lean.Proofs.Proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_positive_caps_pair_straddles
import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Ff
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical
noncomputable section

theorem HardSphereB5.SphericalCrofton.Aux.Endpoint.positive_caps_pair_straddles :
    ∀ (N : ℕ) (n : Fin N → Pt) (h : Fin N → ℝ) (hpos : ∀ i, 0 < h i) (u v p : Pt) (hus : ‖u‖ = 1) (hvs : ‖v‖ = 1) (hpn : ‖p‖ = 1) (hu : ∀ i, h i ≤ inner ℝ (n i) u) (hv : ∀ i, h i ≤ inner ℝ (n i) v) (huv : u ≠ v) (hnon : u ≠ -v) (hpu : inner ℝ p u = 0) (hpv : inner ℝ p v = 0), (∃ a ∈ ⋂ i, cap (n i) (h i), inner ℝ p a < 0) ∧ (∃ b ∈ ⋂ i, cap (n i) (h i), 0 < inner ℝ p b) :=
  @proof_HardSphereB5_SphericalCrofton_Aux_Endpoint_positive_caps_pair_straddles
