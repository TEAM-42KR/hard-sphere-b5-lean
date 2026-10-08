import HardSphereB5Lean.Heads

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean

theorem lensVolFormula :
    ∀ (l : ℝ) (h0 : 0 ≤ l) (h2 : l ≤ 2), lensVol l = π / 12 * (2 - l) ^ 2 * (4 + l) :=
  @HardSphereB5Lean.lensVolFormula
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean

theorem threeBallVolume :
    ∀ (c : Fin 4 → Pt) (X Y s : ℝ)
    (h01 : dist (c 0) (c 1) ^ 2 = 1) (h02 : dist (c 0) (c 2) ^ 2 = 1)
    (h03 : dist (c 0) (c 3) ^ 2 = Y) (h12 : dist (c 1) (c 2) ^ 2 = X)
    (h13 : dist (c 1) (c 3) ^ 2 = 1) (h23 : dist (c 2) (c 3) ^ 2 = s)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < -s ^ 2 + s * X * Y + 2 * s - X ^ 2 * Y - X * Y ^ 2 + 3 * X * Y - 1)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    let a := dist (c i) (c j) ^ 2
    let b := dist (c i) (c k) ^ 2
    let cc := dist (c j) (c k) ^ 2
    let Q := 4 * a * b - (a + b - cc) ^ 2 - a * b * cc
    let g : ℝ → ℝ := fun d => d - d ^ 3 / 12
    (volume (Metric.closedBall (c i) 1 ∩ Metric.closedBall (c j) 1 ∩ Metric.closedBall (c k) 1)).toReal =
      2 * π - 2 / 3 * (Complex.arg ⟨2 * (a + b - cc) - a * b, 2 * √Q⟩
          + Complex.arg ⟨2 * (a + cc - b) - a * cc, 2 * √Q⟩
          + Complex.arg ⟨2 * (b + cc - a) - b * cc, 2 * √Q⟩)
        - (g (√a) * Complex.arg ⟨√a * (b + cc - a), 2 * √Q⟩
          + g (√b) * Complex.arg ⟨√b * (a + cc - b), 2 * √Q⟩
          + g (√cc) * Complex.arg ⟨√cc * (a + b - cc), 2 * √Q⟩)
        + √Q / 6 :=
  @HardSphereB5Lean.threeBallVolume
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean

theorem pathFaceQ_pos :
    ∀ (c : Fin 4 → Pt) (X Y s : ℝ)
    (h01 : dist (c 0) (c 1) ^ 2 = 1) (h02 : dist (c 0) (c 2) ^ 2 = 1)
    (h03 : dist (c 0) (c 3) ^ 2 = Y) (h12 : dist (c 1) (c 2) ^ 2 = X)
    (h13 : dist (c 1) (c 3) ^ 2 = 1) (h23 : dist (c 2) (c 3) ^ 2 = s)
    (hX0 : 0 < X) (hX1 : X < 1) (hY0 : 0 < Y) (hY1 : Y < 1)
    (hH : 0 < -s ^ 2 + s * X * Y + 2 * s - X ^ 2 * Y - X * Y ^ 2 + 3 * X * Y - 1)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k), 0 < 4 * dist (c i) (c j) ^ 2 * dist (c i) (c k) ^ 2
        - (dist (c i) (c j) ^ 2 + dist (c i) (c k) ^ 2 - dist (c j) (c k) ^ 2) ^ 2
        - dist (c i) (c j) ^ 2 * dist (c i) (c k) ^ 2 * dist (c j) (c k) ^ 2 :=
  @HardSphereB5Lean.pathFaceQ_pos
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem kernel_constants :
    alphaK .one = 1 ∧ bK .one = √3 - π / 3 ∧ alphaK .cos = 3 / 4 ∧ bK .cos = √3 / 8 + π / 12 ∧
      (∀ f, cA f = π * alphaK f ∧ cP f = bK f) :=
  @HardSphereB5Lean.kernel_constants
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem kernel_split :
    ∀ (f : Kern) (L : ℝ) (h0 : 0 ≤ L) (hπ : L ≤ π), kK f L = alphaK f * L - bK f + (if L < π / 3 then phiK f L else 0) :=
  @HardSphereB5Lean.kernel_split
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem cutoff_order_two :
    ∀ (f : Kern), phiK f (π / 3) = 0 ∧ deriv (phiK f) (π / 3) = 0 ∧
      ∀ L, deriv (deriv (phiK f)) L = 2 * wK f (Real.cos L) * Real.sin L :=
  @HardSphereB5Lean.cutoff_order_two
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem phiK_nonneg :
    ∀ (f : Kern) (L : ℝ) (h0 : 0 ≤ L) (h1 : L ≤ π / 3), 0 ≤ phiK f L :=
  @HardSphereB5Lean.phiK_nonneg
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem primitive_explicit :
    ∀ (d : ℝ), Pprim .one d = d ^ 2 / 2 + 2 * Real.cos d - 2 + (√3 - π / 3) * d ∧
      Pprim .cos d = (π / 12 + √3 / 8) * d - d ^ 2 / 8 + Real.cos (2 * d) / 8 - 1 / 8 :=
  @HardSphereB5Lean.primitive_explicit
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem rho_rational :
    ∀ (f : Kern) (δ : ℝ), deriv (phiK f) δ / (1 - Real.cos δ ^ 2) = rhoK f (Real.cos δ) :=
  @HardSphereB5Lean.rho_rational
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem sigma_axis_cases :
    (∀ t : ℝ, 0 < t → t < 1 → SigmaD (t • e) = ∅) ∧
      (SigmaD 0 = cap e (1 / 2) ∧ arcA 0 = ∅ ∧ arcB 0 = {u | ‖u‖ = 1 ∧ inner ℝ e u = 1 / 2}) ∧
      (SigmaD e = cap (-e) (1 / 2) ∧ arcB e = ∅ ∧
        arcA e = {u | ‖u‖ = 1 ∧ inner ℝ (-e) u = 1 / 2}) :=
  @HardSphereB5Lean.sigma_axis_cases
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem near_as_spherical :
    ∀ (f : Kern), Jnear f = ∫ D in LamC, Ff f (SigmaD D) :=
  @HardSphereB5Lean.near_as_spherical
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem circInt_isometry_invariant :
    ∀ (p p' : Pt) (R : Pt ≃ₗᵢ[ℝ] Pt) (hR : R e = e), circInt (R p) (R p') = circInt p p' :=
  @HardSphereB5Lean.circInt_isometry_invariant
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem rho_squared_distance :
    ∀ (s : ℝ) (hs0 : 0 < s) (hs4 : s < 4), rhoK .one (1 - s / 2) = 4 * (s - 1) / (s * (4 - s)) ∧
      rhoK .cos (1 - s / 2) = (s - 1) * (3 - s) / (s * (4 - s)) :=
  @HardSphereB5Lean.rho_squared_distance
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem Aface_eq_poly :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (l : Fin 4), Aface c l = Apoly X Y s l :=
  @HardSphereB5Lean.Aface_eq_poly
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem Qface_eq_poly :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (l : Fin 4), Qface c l = Qpoly X Y s l :=
  @HardSphereB5Lean.Qface_eq_poly
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem adjacent_unit_halfwidths :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), betaA c 0 1 2=betaA c 0 2 1 ∧ betaA c 0 1 3=betaA c 1 3 0 :=
  @HardSphereB5Lean.adjacent_unit_halfwidths
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem apex_position_contraction :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), (∑ i, ∑ l, (if l≠i then inner ℝ (c i) (apexTerm c i l) else 0)) = -√(Hpoly X Y s)/4 :=
  @HardSphereB5Lean.apex_position_contraction
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem bulk_apex_anchor :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i l r : Fin 4) (hil : i≠l), inner ℝ (c r-c i) (apexTerm c i l) =
    if r=l then √(Hpoly X Y s)*Lapex c i (oth1 i l) (oth2 i l)/8 else 0 :=
  @HardSphereB5Lean.bulk_apex_anchor
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem bulk_incidence :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s), (∀ l, nRet c l = 1) ∧ ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = 3 :=
  @HardSphereB5Lean.bulk_incidence
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem circumcenter_unique :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), ∃! O : Pt, ∀ i, dist O (c i) ^ 2 = 1 - P4poly X Y s / (4*Hpoly X Y s) :=
  @HardSphereB5Lean.circumcenter_unique
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem circumradius_sq :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), ∃ O : Pt, ∀ i, dist O (c i) ^ 2 = 1 - P4poly X Y s / (4 * Hpoly X Y s) :=
  @HardSphereB5Lean.circumradius_sq
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem common_pair_halfwidth_sum :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s)
    (hP : P4poly X Y s < 0) (i j : Fin 4) (hij : i ≠ j) (hcom : isCommon c i j), π < betaA c i j (oth1 i j) + betaA c i j (oth2 i j) :=
  @HardSphereB5Lean.common_pair_halfwidth_sum
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem coordinate_realization :
    ∀ {X : ℝ} {Y : ℝ} {s : ℝ} (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1) (hH : 0 < Hpoly X Y s), IsPathConfig (canonicalCenters X Y s) X Y s ∧
  ∃ χ : ℝ, 0 < χ ∧ χ < π ∧ s = a0 X Y - b0 X Y * Real.cos χ ∧
    Hpoly X Y s = (b0 X Y) ^ 2 - (a0 X Y - s) ^ 2 :=
  @HardSphereB5Lean.coordinate_realization
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem divergence_path :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), 3*vol c Finset.univ = ∑ i, (pArea c i Finset.univ + inner ℝ (c i) (pMoment c i Finset.univ)) ∧
  ∑ i, pMoment c i Finset.univ = 0 :=
  @HardSphereB5Lean.divergence_path
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem equal_sliver_halves :
    nearCorrection 0 2=Ssliver/2 ∧ nearCorrection 1 3=Ssliver/2 ∧
  nearCorrection 0 1=0 ∧ nearCorrection 1 2=0 ∧ nearCorrection 0 3=0 ∧ nearCorrection 2 3=0 :=
  @HardSphereB5Lean.equal_sliver_halves
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem face_circumcenter_identities :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k), inner ℝ (c j-c i) (faceCircRel c i j k) = q c i j / 2 ∧
  inner ℝ (c k-c i) (faceCircRel c i j k) = q c i k / 2 ∧
  ‖faceCircRel c i j k‖ ^ 2 = q c i j * q c i k * q c j k / Deltaf c i j k ∧
  (∀ ε : ℝ, (ε=1 ∨ ε= -1) → ∀ m ∈ ({i,j,k} : Finset (Fin 4)), dist (triplePoint c i j k ε) (c m)=1) :=
  @HardSphereB5Lean.face_circumcenter_identities
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem face_circumradius_certificate :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (l : Fin 4), (Apoly X Y s l)^2 - 4*Hpoly X Y s*Qface c l =
    -Deltaf c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 * P4poly X Y s :=
  @HardSphereB5Lean.face_circumradius_certificate
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem labeled_patch_continuous_distinct :
    ∀ (c : Fin 4 → Pt) (hinj : Function.Injective c) (i : Fin 4), ContinuousAt (fun c : Fin 4 → Pt => pArea c i Finset.univ) c ∧
  ContinuousAt (fun c : Fin 4 → Pt => pMoment c i Finset.univ) c :=
  @HardSphereB5Lean.labeled_patch_continuous_distinct
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem midpoint_values :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s),
    let M := (1/2 : ℝ) • (c 0+c 1)
  dist M (c 0)^2=1/4 ∧ dist M (c 1)^2=1/4 ∧
  dist M (c 2)^2=(1+2*X)/4 ∧ dist M (c 3)^2=(1+2*Y)/4 :=
  @HardSphereB5Lean.midpoint_values
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem near_arc_inventory :
    (∑ i, ∑ j, (if i<j then nearPairArc i j else 0)) =
  4*triangleSide 0 1 2 3 + 2*triangleSide 1 2 0 3 + 2*triangleSide 0 2 3 1 +
  2*triangleSide 0 3 2 1 + 2*triangleSide 2 3 0 1 +
  bulkSource 0 1 + 2*bulkSource 0 2 + 2*bulkSource 1 2 + bulkSource 2 3 + Ssliver :=
  @HardSphereB5Lean.near_arc_inventory
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem near_common_pair_acute_obtuse :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s)
    (hs : s < 1) (hP : P4poly X Y s < 0), (Y < X → betaA c 0 2 1 < π / 2 ∧ π / 2 < betaA c 0 2 3) ∧
    (X < Y → betaA c 1 3 0 < π / 2 ∧ π / 2 < betaA c 1 3 2) :=
  @HardSphereB5Lean.near_common_pair_acute_obtuse
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem near_dihedral_identity :
    ∀ (X Y s : ℝ), (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) ^ 2 + 4 * s * Hpoly X Y s =
      (4 * s - (1 + s - Y) ^ 2) * (4 * s * X - (X + s - 1) ^ 2) :=
  @HardSphereB5Lean.near_dihedral_identity
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem near_face_inventory :
    (∑ l, VfaceIntegral l)=2*Vadj+2*Vnon ∧ (∑ l, EfaceIntegral l)=2*Eadj+2*Enon :=
  @HardSphereB5Lean.near_face_inventory
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem near_moving_point_width :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs : s < 1), phiE c 2 3 = atan2 (2 * √(s * Hpoly X Y s)) (X * Y + (s - 1) * (X + Y) + 1 - s ^ 2) ∧
    (0 < P4poly X Y s → ell c 2 3 =
        atan2 (2 * √(Qpoly X Y s 1)) (√s * (1 + Y - s))
          + atan2 (2 * √(Qpoly X Y s 0)) (√s * (1 + X - s)) - phiE c 2 3) ∧
    (P4poly X Y s < 0 → Y < X → ell c 2 3 = 2 * atan2 (2 * √(Qpoly X Y s 1)) (√s * (1 + Y - s))) ∧
    (P4poly X Y s < 0 → X < Y → ell c 2 3 = 2 * atan2 (2 * √(Qpoly X Y s 0)) (√s * (1 + X - s))) :=
  @HardSphereB5Lean.near_moving_point_width
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem near_pair23_halfwidths_acute :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs : s < 1), betaA c 2 3 0 < π / 2 ∧ betaA c 2 3 1 < π / 2 :=
  @HardSphereB5Lean.near_pair23_halfwidths_acute
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem near_selector_certificates :
    ∀ (X Y s t : ℝ), P4poly X Y s = -Y*(4-Y)*X^2+2*Y*(s+5-2*Y)*X-3*(s-1)^2 ∧
  Y^2*(s+5-2*Y)^2-3*Y*(4-Y)*(s-1)^2=4*Y*(3-Y)*Qpoly X Y s 1 ∧
  Hpoly Y Y s = (s-s0 Y)*(1+2*Y-s) ∧
  P4poly Y Y (1-t) = (Y*(2-Y)-t)*(Y*(6-Y)+3*t) ∧
  P4poly 1 Y (1-t) = Y*(1-Y)^2*(8-3*Y)+(Y*(2-Y)-t)*(3*(Y*(2-Y)+t)+2*Y) ∧
  Hpoly X Y (s0 Y) = -Y*(X-Y)*(X-(2-Y)^2) :=
  @HardSphereB5Lean.near_selector_certificates
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem near_selector_counts :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs0 : 0<s) (hs : s<1) (hP : P4poly X Y s ≠ 0), ((Bminus Y s<X → nearCounts c=(1,1)) ∧
   (X<Bminus Y s → s<s0 Y → nearCounts c=(2,0)) ∧
   (X<Bminus Y s → s0 Y<s → nearCounts c=(0,2))) ∧
  (Bminus Y s<X ∨ (X<Bminus Y s ∧ s<s0 Y) ∨ (X<Bminus Y s ∧ s0 Y<s)) :=
  @HardSphereB5Lean.near_selector_counts
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem near_selector_factorization :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs0 : 0<s) (hs : s<1) (hP : P4poly X Y s ≠ 0), P4poly X Y s = Y*(4-Y)*(X-Bminus Y s)*(Bplus Y s-X) ∧
  1 < Bplus Y s ∧ (0<P4poly X Y s ↔ Bminus Y s<X) :=
  @HardSphereB5Lean.near_selector_factorization
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem near_selector_sliver_order :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs0 : 0<s) (hs : s<1) (hP : P4poly X Y s<0), (Y<X ↔ s<s0 Y) ∧ (X<Y ↔ s0 Y<s) :=
  @HardSphereB5Lean.near_selector_sliver_order
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem near_selector_wall_bulk :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (heq : s=s0 Y), Y<X ∧ 0<P4poly X Y s :=
  @HardSphereB5Lean.near_selector_wall_bulk
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem no_near_sliver_on_diagonal :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hs : s < 1) (hXY : X = Y), 0 < P4poly X Y s :=
  @HardSphereB5Lean.no_near_sliver_on_diagonal
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem no_sliver_at_s_one :
    ∀ {X : ℝ} {Y : ℝ} (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1), 0 < P4poly X Y 1 :=
  @HardSphereB5Lean.no_sliver_at_s_one
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem obtuse_point_values :
    Hpoly (3 / 4) (1 / 4) (11 / 32) = 9 / 1024 ∧ P4poly (3 / 4) (1 / 4) (11 / 32) = -3 / 1024 :=
  @HardSphereB5Lean.obtuse_point_values
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem obtuse_sentence_counterexample :
    ∀ {c : Fin 4 → Pt} (hc : IsPathConfig c (3 / 4) (1 / 4) (11 / 32)), isCommon c 0 2 ∧ betaA c 0 2 1 < π / 2 ∧ π / 2 < betaA c 0 2 3 ∧
      ell c 0 2 = 2 * betaA c 0 2 1 + 2 * betaA c 0 2 3 - 2 * π :=
  @HardSphereB5Lean.obtuse_sentence_counterexample
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem pair_arc_normalizer :
    ∀ (a b cc : ℝ), DeltaT a b cc * (4-a) = a*(b+cc-a)^2+4*QT a b cc ∧
  (2*(a+b-cc)-a*b)^2+4*QT a b cc = a*b*(4-a)*(4-b) :=
  @HardSphereB5Lean.pair_arc_normalizer
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem pair_replacement_body :
    ∀ (x : Fin 3 → Pt) (hnd : AffineIndependent ℝ x)
 (ha4 : dist (x 1) (x 2)^2<4) (hb : dist (x 0) (x 1)^2≤1) (hcc : dist (x 0) (x 2)^2≤1)
 (hlong : dist (x 0) (x 1)^2≤dist (x 1) (x 2)^2 ∧ dist (x 0) (x 2)^2≤dist (x 1) (x 2)^2)
 (hQ : QT (dist (x 1) (x 2)^2) (dist (x 1) (x 0)^2) (dist (x 2) (x 0)^2)≤0), (⋂ i, Metric.closedBall (x i) 1)=Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1 :=
  @HardSphereB5Lean.pair_replacement_body
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem pair_replacement_conditional :
    ∀ (x : Fin 3 → Pt) (hnd : AffineIndependent ℝ x)
    (ha4 : dist (x 1) (x 2) ^ 2 < 4) (hb : dist (x 0) (x 1) ^ 2 ≤ 1) (hcc : dist (x 0) (x 2) ^ 2 ≤ 1)
    (hlong : dist (x 0) (x 1) ^ 2 ≤ dist (x 1) (x 2) ^ 2 ∧ dist (x 0) (x 2) ^ 2 ≤ dist (x 1) (x 2) ^ 2)
    (hQ : QT (dist (x 1) (x 2) ^ 2) (dist (x 1) (x 0) ^ 2) (dist (x 2) (x 0) ^ 2) ≤ 0), (volume (⋂ i, Metric.closedBall (x i) 1)).toReal = V2 (dist (x 1) (x 2)) :=
  @HardSphereB5Lean.pair_replacement_conditional
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem pair_replacement_unrestricted_false :
    ∃ x : Fin 3 → Pt, (∀ i j, i ≠ j → dist (x i) (x j) ^ 2 = 7 / 2) ∧
      QT (7 / 2) (7 / 2) (7 / 2) ≤ 0 ∧ (⋂ i, Metric.closedBall (x i) 1) = ∅ ∧
      0 < (volume (Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1)).toReal :=
  @HardSphereB5Lean.pair_replacement_unrestricted_false
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem pair_width :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (i j : Fin 4) (hij : i ≠ j), ell c i j = (nRet c (oth2 i j) : ℝ) * betaA c i j (oth1 i j)
        + (nRet c (oth1 i j) : ℝ) * betaA c i j (oth2 i j)
        - (if 0 < P4poly X Y s then phiE c i j else 0)
        - (if P4poly X Y s < 0 ∧ isCommon c i j then 2 * π else 0) :=
  @HardSphereB5Lean.pair_width
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem positive_volume_active_patches :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), 0 < vol c Finset.univ ∧ (∀ i, 0 < pArea c i Finset.univ) ∧
      ∀ i, Nonempty (patch c i ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  @HardSphereB5Lean.positive_volume_active_patches
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem raw_arc_decompositions_exist :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0), Nonempty (∀ e : PairIndex, PairArcDecomposition c e.1.1 e.1.2) :=
  @HardSphereB5Lean.raw_arc_decompositions_exist
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem raw_endpoint_contraction :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0)
  (D : ∀ e : PairIndex, PairArcDecomposition c e.1.1 e.1.2), rawEndpointSum c D = ((∑ l, (nRet c l : ℝ)*√(Qface c l)) -
    (if 0<P4poly X Y s then √(Hpoly X Y s) else 0)) / 2 :=
  @HardSphereB5Lean.raw_endpoint_contraction
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem realizable :
    ∀ {X : ℝ} {Y : ℝ} {s : ℝ} (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1) (hH : 0 < Hpoly X Y s), ∃ c : Fin 4 → Pt, IsPathConfig c X Y s :=
  @HardSphereB5Lean.realizable
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem retained_vertex_count :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0), ∑ l, nRet c l = 4 :=
  @HardSphereB5Lean.retained_vertex_count
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem sliver_incidence :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0), (∀ l, nRet c l = if 0 < Qpoly X Y s l ∧ Apoly X Y s l < 0 then 2 else 0) ∧
      ∑ l, nRet c l = 4 ∧
      ∃ i j, i ≠ j ∧ isCommon c i j ∧
        ∀ m, ∑ l ∈ Finset.univ.erase m, nRet c l = if m = i ∨ m = j then 4 else 2 :=
  @HardSphereB5Lean.sliver_incidence
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem sliver_lens_covered :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (i j : Fin 4) (hij : i≠j) (hcom : isCommon c i j), body c {i,j} ⊆ Metric.closedBall (c (oth1 i j)) 1 ∪ Metric.closedBall (c (oth2 i j)) 1 :=
  @HardSphereB5Lean.sliver_lens_covered
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem sliver_patch_valuation :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (i j : Fin 4)
    (hij : i ≠ j) (hcom : isCommon c i j) (m : Fin 4), pArea c m Finset.univ =
        pArea c m {i, j, oth1 i j} + pArea c m {i, j, oth2 i j} - pArea c m {i, j} ∧
      pMoment c m Finset.univ =
        pMoment c m {i, j, oth1 i j} + pMoment c m {i, j, oth2 i j} - pMoment c m {i, j} :=
  @HardSphereB5Lean.sliver_patch_valuation
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem sliver_table :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0), (s < 1 → Y < X → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (2, 0, 2, 0) ∧ isCommon c 0 2) ∧
    (s < 1 → X < Y → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (0, 2, 0, 2) ∧ isCommon c 1 3) ∧
    (1 < s → (nRet c 3, nRet c 2, nRet c 1, nRet c 0) = (0, 0, 2, 2) ∧ isCommon c 2 3) :=
  @HardSphereB5Lean.sliver_table
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem sliver_volume :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s < 0) (i j : Fin 4)
    (hij : i ≠ j) (hcom : isCommon c i j), vol c Finset.univ = vol c {i, j, oth1 i j} + vol c {i, j, oth2 i j} - V2 (dist (c i) (c j)) :=
  @HardSphereB5Lean.sliver_volume
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem support_factor_identities :
    ∀ (X Y : ℝ) (hX : 0 < X) (hX1 : X < 1) (hY : 0 < Y) (hY1 : Y < 1), (a0 X Y) ^ 2 - (b0 X Y) ^ 2 = (1-X)*(1-Y)+X*(1-Y)^2+Y*(1-X)^2 ∧
  (3-a0 X Y) ^ 2 - (b0 X Y) ^ 2 = (1-X)*(4-X*Y)+X*(1-Y)*(4-Y) :=
  @HardSphereB5Lean.support_factor_identities
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem tetrahedron_metric :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), 0 < s ∧ s < 3 ∧ AffineIndependent ℝ c ∧
  (∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < Deltaf c i j k) ∧
  (det3 (c 1-c 0) (c 2-c 0) (c 3-c 0)) ^ 2 = Hpoly X Y s / 4 :=
  @HardSphereB5Lean.tetrahedron_metric
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem triple_patch_area :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k), pArea c i {i, j, k} =
      2 * π - 2 * gammaA c i j k - √(q c i j) * betaA c i j k - √(q c i k) * betaA c i k j :=
  @HardSphereB5Lean.triple_patch_area
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem triple_patch_moment :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k), pMoment c i {i, j, k} =
      ((1 - q c i j / 4) / √(q c i j) * betaA c i j k) • (c j - c i)
        + ((1 - q c i k / 4) / √(q c i k) * betaA c i k j) • (c k - c i)
        + (√(Qf c i j k) / Deltaf c i j k) •
            cross ((c j - c i) - (c k - c i)) (cross (c j - c i) (c k - c i)) :=
  @HardSphereB5Lean.triple_patch_moment
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem triple_patch_moment_scalar :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k : Fin 4) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (cs : Pt), inner ℝ (cs - c i) (pMoment c i {i, j, k}) =
      (1 - q c i j / 4) * inner ℝ (cs - c i) (c j - c i) * betaA c i j k / √(q c i j)
        + (1 - q c i k / 4) * inner ℝ (cs - c i) (c k - c i) * betaA c i k j / √(q c i k)
        + √(Qf c i j k) * ((q c i j - q c i k - q c j k) * inner ℝ (cs - c i) (c j - c i)
            - (q c i j - q c i k + q c j k) * inner ℝ (cs - c i) (c k - c i)) /
          (2 * Deltaf c i j k) :=
  @HardSphereB5Lean.triple_patch_moment_scalar
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem triple_retention_test :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (i j k l : Fin 4)
  (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l)
  (ε : ℝ) (hε : ε=1 ∨ ε= -1), dist (triplePoint c i j k ε) (c l) ^ 2 - 1 =
    q c i l - 2*inner ℝ (c l-c i) (faceCircRel c i j k) -
      ε * 4*√(Qf c i j k) / Deltaf c i j k * det3 (c j-c i) (c k-c i) (c l-c i) :=
  @HardSphereB5Lean.triple_retention_test
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem volume_continuous :
    Continuous (fun c : Fin 4 → Pt => vol c Finset.univ) :=
  @HardSphereB5Lean.volume_continuous
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem walls_null :
    volume wallSet = 0 :=
  @HardSphereB5Lean.walls_null
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem walls_pathMeasure_null :
    pathMeasure wallSet = 0 :=
  @HardSphereB5Lean.walls_pathMeasure_null
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem weighted_apex_coefficient :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s), Lapex c 3 0 2 = (2*Y*s-Y^2-s^2+Y+s)/(4*Y*s-(Y+s-1)^2) :=
  @HardSphereB5Lean.weighted_apex_coefficient
end
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem AB_chain :
    ∀ (f : Kern), ABint f = Ic f + frakB f :=
  @HardSphereB5Lean.AB_chain
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem Rsame_label_symmetry :
    ∀ (f : Kern), Rsame f = 2 * ∫ D in LamC, AAf f D :=
  @HardSphereB5Lean.Rsame_label_symmetry
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem capInter_isRegularRegionCrofton :
    ∀ (N : ℕ) (hN : 0 < N) (n : Fin N → Pt) (h : Fin N → ℝ)
    (hn : ∀ m, ‖n m‖ = 1) (h0 : ∀ m, 0 ≤ h m)
    (hint : (sInterior (⋂ m, cap (n m) (h m))).Nonempty), IsRegularRegionCrofton (⋂ m, cap (n m) (h m)) :=
  @HardSphereB5Lean.capInter_isRegularRegionCrofton
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem chord_length_integral :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K), gcIntegral (fun G => if 0 < chordLen K G then chordLen K G else 0) = π * sArea K :=
  @HardSphereB5Lean.chord_length_integral
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem chord_representation :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern), Ff f K = gcIntegral (fun G => if 0 < chordLen K G then kK f (chordLen K G) else 0) :=
  @HardSphereB5Lean.chord_representation
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem coarea_transport :
    ∀ (f : Kern), frakB f = ∫ p in FA, ∫ p' in FB,
      (if 0 < dist p p' ∧ dist p p' < 1 then
          rhoK f (1 - dist p p' ^ 2 / 2) / dist p p' * circInt p p' else 0)
        ∂(sphereMeasure e) ∂(sphereMeasure 0) :=
  @HardSphereB5Lean.coarea_transport
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem crofton_decomposition :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern), Ff f K = cA f * sArea K - cP f * perim K + Rf f K :=
  @HardSphereB5Lean.crofton_decomposition
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem cross_arc_by_parts :
    ∀ (f : Kern) (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D)
    (hR : Rc ‖D‖ ‖D - e‖ < 1), ABf f D = 2 * Pprim f (min (deltaV D) (π / 3)) + Bf f D :=
  @HardSphereB5Lean.cross_arc_by_parts
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem definition_chain :
    ∀ (f : Kern), Jnear f = ECr f + Rsame f + ABint f :=
  @HardSphereB5Lean.definition_chain
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem flat_measure_general :
    ∀ (K : Pt → Pt → ℝ)
    (hint : Integrable (Function.uncurry K)
      (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)))
    (hrot : ∀ R, IsAxialRotation R → ∀ p ∈ FA, ∀ p' ∈ FB, K (R p) (R p') = K p p'), ∫ p in FA, ∫ p' in FB, K p p' ∂(sphereMeasure e) ∂(sphereMeasure 0) =
      π / 2 * ∫ v in Dfull,
        (K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) +
            K (pRep v.1) (pRep2 v.2.1 (-chiPlus v.1 v.2.1 v.2.2))) / √(Hpoly v.1 v.2.1 v.2.2) :=
  @HardSphereB5Lean.flat_measure_general
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem flat_measure_reflection_even :
    ∀ (K : Pt → Pt → ℝ)
    (hint : Integrable (Function.uncurry K)
      (((sphereMeasure 0).restrict FA).prod ((sphereMeasure e).restrict FB)))
    (hinv : ∀ R : Pt ≃ₗᵢ[ℝ] Pt, R e = e → ∀ p ∈ FA, ∀ p' ∈ FB, K (R p) (R p') = K p p'), ∫ p in FA, ∫ p' in FB, K p p' ∂(sphereMeasure e) ∂(sphereMeasure 0) =
      π * ∫ v in Dfull,
        K (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) / √(Hpoly v.1 v.2.1 v.2.2) :=
  @HardSphereB5Lean.flat_measure_reflection_even
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem flat_measure_target :
    ∀ (f : Kern), frakB f = π * ∫ v in Dnear,
      (1 / √(Hpoly v.1 v.2.1 v.2.2)) * (rhoK f (1 - v.2.2 / 2) / √v.2.2) *
        circInt (pRep v.1) (pRep2 v.2.1 (chiPlus v.1 v.2.1 v.2.2)) :=
  @HardSphereB5Lean.flat_measure_target
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem hit_mass :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K), gcIntegral (fun G => if 0 < chordLen K G then 1 else 0) = perim K :=
  @HardSphereB5Lean.hit_mass
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem literal_crofton_false :
    ∀ (n : Pt) (hn : ‖n‖ = 1) (f : Kern), Ff f (cap n (Real.cos (π / 6))) ≠
      cA f * sArea (cap n (Real.cos (π / 6))) - cP f * perim (cap n (Real.cos (π / 6)))
        + RfAll f (cap n (Real.cos (π / 6))) :=
  @HardSphereB5Lean.literal_crofton_false
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem literal_remainder_excess :
    ∀ {K : Set Pt} (hK : IsRegularRegionCrofton K) (f : Kern), RfAll f K = Rf f K + bK f * (2 * π - perim K) :=
  @HardSphereB5Lean.literal_remainder_excess
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem sigma_support :
    ∀ (D : Pt) (hD : D ∈ LamC) (hoff : offAxis D), (Rc ‖D‖ ‖D - e‖ < 1 → 0 < sArea (SigmaD D) ∧ ∃ V W, V ≠ W ∧ vertsD D = {V, W}) ∧
      (Rc ‖D‖ ‖D - e‖ = 1 → ∃ V, SigmaD D = {V}) ∧
      (1 < Rc ‖D‖ ‖D - e‖ → SigmaD D = ∅) :=
  @HardSphereB5Lean.sigma_support
end

section
set_option autoImplicit false
open MeasureTheory Real SphereGeom HardSphereB5.SphericalCrofton
open HardSphereB5.Lean (Pt e)
open scoped Classical

theorem spherical_remainder_split :
    ∀ (f : Kern) (D : Pt) (hD : D ∈ LamC), Rf f (SigmaD D) = AAf f D + BBf f D + ABf f D :=
  @HardSphereB5Lean.spherical_remainder_split
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5_Lean_Geometry_PathCore_bulk_patch_area :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s) (i : Fin 4), pArea c i Finset.univ = -π + (1 / 2) * ∑ l, (if l ≠ i then pArea c i (faceSet l) else 0)
      + (1 / 2) * ∑ j, (if j ≠ i then dist (c i) (c j) * phiE c i j else 0) :=
  @HardSphereB5Lean.HardSphereB5_Lean_Geometry_PathCore_bulk_patch_area
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5_Lean_Geometry_PathCore_bulk_patch_moment :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s) (i : Fin 4), pMoment c i Finset.univ =
      (1 / 2 : ℝ) • ∑ l, (if l ≠ i then pMoment c i (faceSet l) else 0)
        - (1 / 2 : ℝ) • ∑ j, (if j ≠ i then
            ((1 - q c i j / 4) / √(q c i j) * phiE c i j) • (c j - c i) else 0)
        + ∑ l, (if l ≠ i then apexTerm c i l else 0) :=
  @HardSphereB5Lean.HardSphereB5_Lean_Geometry_PathCore_bulk_patch_moment
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section

theorem HardSphereB5_Lean_Geometry_PathCore_bulk_volume :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : 0 < P4poly X Y s), vol c Finset.univ = (1 / 2) * ∑ l, vol c (faceSet l) - 4 * π / 3
      + (1 / 2) * ∑ i, ∑ j, (if i < j then g (dist (c i) (c j)) * phiE c i j else 0)
      - √(Hpoly X Y s) / 12 :=
  @HardSphereB5Lean.HardSphereB5_Lean_Geometry_PathCore_bulk_volume
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5_Lean_Geometry_PathCore_near_volume_inventory :
    Kcap=2*Vadj+2*Vnon+Ccap+Dcap+2*Eadj+2*Enon +
  (∑ i, ∑ j, (if i<j then nearPairArc i j else 0)) :=
  @HardSphereB5Lean.HardSphereB5_Lean_Geometry_PathCore_near_volume_inventory
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5_Lean_Geometry_PathCore_normal_form_patch :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0) (i : Fin 4), pArea c i Finset.univ =
        2 * π - ∑ l, (if l ≠ i then (nRet c l : ℝ) * gammaA c i (oth1 i l) (oth2 i l) else 0)
          - (1 / 2) * ∑ j, (if j ≠ i then dist (c i) (c j) * ell c i j else 0) ∧
      pMoment c i Finset.univ =
        (1 / 2 : ℝ) • ∑ j, (if j ≠ i then
            ((1 - q c i j / 4) / dist (c i) (c j) * ell c i j) • (c j - c i) else 0)
          + ∑ l, (if l ≠ i then
              ((nRet c l : ℝ) * √(Qface c l) / (2 * Deltaf c i (oth1 i l) (oth2 i l))) •
                endTerm c i l else 0)
          + (if 0 < P4poly X Y s then ∑ l, (if l ≠ i then apexTerm c i l else 0) else 0) :=
  @HardSphereB5Lean.HardSphereB5_Lean_Geometry_PathCore_normal_form_patch
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5_Lean_Geometry_PathCore_normal_form_volume :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s ≠ 0), vol c Finset.univ = 8 * π / 3 - (1 / 3) * ∑ l, (nRet c l : ℝ) * sigmaF c l
      - (1 / 2) * ∑ i, ∑ j, (if i < j then g (dist (c i) (c j)) * ell c i j else 0)
      + (1 / 12) * ∑ l, (nRet c l : ℝ) * √(Qface c l)
      - (if 0 < P4poly X Y s then √(Hpoly X Y s) / 12 else 0) :=
  @HardSphereB5Lean.HardSphereB5_Lean_Geometry_PathCore_normal_form_volume
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_volume :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0)
  (D : ∀ e : PairIndex, PairArcDecomposition c e.1.1 e.1.2), vol c Finset.univ = 8*π/3 - (1/3)*∑ l, (nRet c l : ℝ)*sigmaF c l -
    (1/2)*∑ i, ∑ j, (if i<j then g (dist (c i) (c j))*ell c i j else 0) + rawEndpointSum c D / 6 :=
  @HardSphereB5Lean.HardSphereB5_Lean_Geometry_PathCore_raw_endpoint_volume
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem HardSphereB5_Lean_Geometry_PathCore_weighted_channel_normal_form :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ} (hc : IsPathConfig c X Y s) (hP : P4poly X Y s≠0) (h ε : ℝ)
  (hchannel : (h=channelH2 Y ∧ ε= -1) ∨ (h=channelH3 X Y s ∧ ε=1)), channelDensity c X h ε = 4*π*hcWeight X*h -
    (∑ i, ∑ j, (if i<j then channelArcCoeff c X h ε i j * ell c i j else 0)) +
    channelCorner c X h + channelEndpoint c X Y s h ε :=
  @HardSphereB5Lean.HardSphereB5_Lean_Geometry_PathCore_weighted_channel_normal_form
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem pair_replacement_patch_ae :
    ∀ (x : Fin 3 → Pt) (hnd : AffineIndependent ℝ x)
    (ha4 : dist (x 1) (x 2) ^ 2 < 4) (hb : dist (x 0) (x 1) ^ 2 ≤ 1) (hcc : dist (x 0) (x 2) ^ 2 ≤ 1)
    (hlong : dist (x 0) (x 1) ^ 2 ≤ dist (x 1) (x 2) ^ 2 ∧ dist (x 0) (x 2) ^ 2 ≤ dist (x 1) (x 2) ^ 2)
    (hQ : QT (dist (x 1) (x 2) ^ 2) (dist (x 1) (x 0) ^ 2) (dist (x 2) (x 0) ^ 2) ≤ 0) (i : Fin 3), ((⋂ j, Metric.closedBall (x j) 1 : Set Pt)) =ᵐ[SphereGeom.sphereMeasure (x i)]
      ((if i = 0 then ∅ else Metric.closedBall (x 1) 1 ∩ Metric.closedBall (x 2) 1 : Set Pt)) :=
  @HardSphereB5Lean.pair_replacement_patch_ae
end
end

section
set_option autoImplicit false
open MeasureTheory Real HardSphereB5.Lean HardSphereB5.Lean.Geometry.PathCore
noncomputable section
open scoped Classical

theorem realizable_classification :
    ∀ {c : Fin 4 → Pt} {X : ℝ} {Y : ℝ} {s : ℝ}
    (hc : IsPathConfig c X Y s), ∃ φ : Pt ≃ᵃⁱ[ℝ] Pt, ∀ i, φ (c i) = canonicalCenters X Y s i :=
  @HardSphereB5Lean.realizable_classification
end
end
