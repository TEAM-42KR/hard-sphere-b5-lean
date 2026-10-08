import HardSphereB5Lean.Definitions.Def_HardSphereB5_SphericalCrofton_Aux_Endpoint_boundaryTau
set_option autoImplicit false
noncomputable section
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
namespace HardSphereB5.SphericalCrofton.Aux.Endpoint

structure CircleEndpointAtlas where
  c : Fin 2 → Pt
  frame : Fin 2 → Fin 2 → Pt
  r : Fin 2 → ℝ
  T : Fin 2 → ℝ

def atlasCircle (C : CircleEndpointAtlas) (i : Fin 2) (t : ℝ) : Pt :=
  circlePt (C.c i) (C.frame i 0) (C.frame i 1) (C.r i) t

def atlasGamma (C : CircleEndpointAtlas) (t : ℝ) : Pt :=
  if t < 0 then atlasCircle C 0 (t + (2 * Real.pi + 1))
  else atlasCircle C 1 (t - 1)

def atlasInterval (C : CircleEndpointAtlas) : Set ℝ :=
  Set.Ioo (-(2 * Real.pi + 1)) (-(2 * Real.pi + 1) + C.T 0) ∪
    Set.Ioo 1 (1 + C.T 1)

def atlasSpeed (C : CircleEndpointAtlas) (t : ℝ) : ℝ :=
  if t < 0 then C.r 0 else C.r 1

def atlasSourceMu (C : CircleEndpointAtlas) : Measure ℝ :=
  (volume.restrict (atlasInterval C)).withDensity (fun t => ENNReal.ofReal (atlasSpeed C t))

structure IsCircleEndpointAtlas (D : Pt) (C : CircleEndpointAtlas) : Prop where
  orthonormal : ∀ i, Orthonormal ℝ (C.frame i)
  radius_pos : ∀ i, 0 < C.r i
  width_nonneg : ∀ i, 0 ≤ C.T i
  width_le : ∀ i, C.T i ≤ 2 * Real.pi
  unit : ∀ t ∈ atlasInterval C, ‖atlasGamma C t‖ = 1
  injective : Set.InjOn (atlasGamma C) (atlasInterval C)
  tangent : ∀ t ∈ atlasInterval C, ∃ k : ℝ,
    deriv (atlasGamma C) t = k • boundaryTau D (atlasGamma C t) ∧ |k| = atlasSpeed C t
  source_map : (atlasSourceMu C).map (atlasGamma C) = boundaryMu D
  frontier_cover : ∃ F : Set Pt, F.Finite ∧
    atlasGamma C '' atlasInterval C = sFrontier (SigmaD D) \ F

def atlasPair (C : CircleEndpointAtlas) (x : Pt) : Pt × Pt :=
  (atlasGamma C (x 0), atlasGamma C (x 1))

def atlasRadial (C : CircleEndpointAtlas) (x : Pt) : Pt :=
  x 2 • unitDir (cross (atlasGamma C (x 0)) (atlasGamma C (x 1)))

def atlasRadialSource (C : CircleEndpointAtlas) : Set Pt :=
  {x | x 0 ∈ atlasInterval C ∧ x 1 ∈ atlasInterval C ∧
    x 2 ∈ Set.Ioo (0 : ℝ) 1 ∧ cross (atlasGamma C (x 0)) (atlasGamma C (x 1)) ≠ 0}

end HardSphereB5.SphericalCrofton.Aux.Endpoint
