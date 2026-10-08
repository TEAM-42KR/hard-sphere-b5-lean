import Mathlib
import HardSphereB5Lean.Definitions.Def_SolidGeom_ClassicalInputs_SurfaceCalculusInputs
import HardSphereB5Lean.Definitions.Def_HardSphereB5_Lean_b5
import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

noncomputable section
open MeasureTheory Real

namespace HardSphereB5.Lean.Geometry.PathCore

open HardSphereB5.Lean (Pt)
open scoped Classical

def atan2 (y x : ℝ) : ℝ := Complex.arg ⟨x, y⟩

abbrev sphereMeasure (c : Pt) : Measure Pt := SphereGeom.sphereMeasure c

abbrev cross (u v : Pt) : Pt := SphereGeom.cross u v

def det3 (u v w : Pt) : ℝ := inner ℝ (cross u v) w

def g (d : ℝ) : ℝ := d - d ^ 3 / 12

def V2 (d : ℝ) : ℝ := π * (4 / 3 - d + d ^ 3 / 12)

def Hpoly (X Y s : ℝ) : ℝ := -s ^ 2 + s * X * Y + 2 * s - X ^ 2 * Y - X * Y ^ 2 + 3 * X * Y - 1

def P4poly (X Y s : ℝ) : ℝ :=
  -3 * s ^ 2 + 2 * s * X * Y + 6 * s + X ^ 2 * Y ^ 2 - 4 * X ^ 2 * Y - 4 * X * Y ^ 2 + 10 * X * Y - 3

def q (c : Fin 4 → Pt) (i j : Fin 4) : ℝ := dist (c i) (c j) ^ 2

structure IsPathConfig (c : Fin 4 → Pt) (X Y s : ℝ) : Prop where
  q01 : q c 0 1 = 1
  q02 : q c 0 2 = 1
  q03 : q c 0 3 = Y
  q12 : q c 1 2 = X
  q13 : q c 1 3 = 1
  q23 : q c 2 3 = s
  X_pos : 0 < X
  X_lt_one : X < 1
  Y_pos : 0 < Y
  Y_lt_one : Y < 1
  H_pos : 0 < Hpoly X Y s

def body (c : Fin 4 → Pt) (F : Finset (Fin 4)) : Set Pt := ⋂ n ∈ F, Metric.closedBall (c n) 1

def Kset (c : Fin 4 → Pt) : Set Pt := body c Finset.univ

def vol (c : Fin 4 → Pt) (F : Finset (Fin 4)) : ℝ := (volume (body c F)).toReal

def pArea (c : Fin 4 → Pt) (m : Fin 4) (F : Finset (Fin 4)) : ℝ :=
  if m ∈ F then (sphereMeasure (c m) (body c F)).toReal else 0

def pMoment (c : Fin 4 → Pt) (m : Fin 4) (F : Finset (Fin 4)) : Pt :=
  if m ∈ F then ∫ x in body c F, (x - c m) ∂(sphereMeasure (c m)) else 0

def patch (c : Fin 4 → Pt) (i : Fin 4) : Set Pt := Metric.sphere (c i) 1 ∩ Kset c

def faceVerts (l : Fin 4) : Fin 4 × Fin 4 × Fin 4 :=
  ![((1 : Fin 4), (2 : Fin 4), (3 : Fin 4)), (0, 2, 3), (0, 1, 3), (0, 1, 2)] l

def faceSet (l : Fin 4) : Finset (Fin 4) := Finset.univ.erase l

def DeltaT (a b cc : ℝ) : ℝ := 4 * a * b - (a + b - cc) ^ 2

def QT (a b cc : ℝ) : ℝ := DeltaT a b cc - a * b * cc

def Qf (c : Fin 4 → Pt) (i j k : Fin 4) : ℝ := QT (q c i j) (q c i k) (q c j k)

def Deltaf (c : Fin 4 → Pt) (i j k : Fin 4) : ℝ := DeltaT (q c i j) (q c i k) (q c j k)

def Qface (c : Fin 4 → Pt) (l : Fin 4) : ℝ :=
  Qf c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2

def Qpoly (X Y s : ℝ) : Fin 4 → ℝ :=
  ![-X ^ 2 + X * s + 2 * X - s ^ 2 + 2 * s - 1, -Y ^ 2 + Y * s + 2 * Y - s ^ 2 + 2 * s - 1,
    Y * (3 - Y), X * (3 - X)]

def Apoly (X Y s : ℝ) : Fin 4 → ℝ :=
  ![-X ^ 2 * Y + X * Y * s + X * Y - X * s + X - s ^ 2 + 2 * s - 1,
    -X * Y ^ 2 + X * Y * s + X * Y - Y * s + Y - s ^ 2 + 2 * s - 1,
    Y * (-X * Y + 2 * X + s - 1), X * (-X * Y + 2 * Y + s - 1)]

def triplePts (c : Fin 4 → Pt) (l : Fin 4) : Set Pt := {x | ∀ i, i ≠ l → dist x (c i) = 1}

def nRet (c : Fin 4 → Pt) (l : Fin 4) : ℕ :=
  if 0 < Qface c l then (triplePts c l ∩ Kset c).ncard else 0

def gammaA (c : Fin 4 → Pt) (i j k : Fin 4) : ℝ :=
  atan2 (2 * √(Qf c i j k)) (2 * (q c i j + q c i k - q c j k) - q c i j * q c i k)

def betaA (c : Fin 4 → Pt) (i j k : Fin 4) : ℝ :=
  atan2 (2 * √(Qf c i j k)) (√(q c i j) * (q c i k + q c j k - q c i j))

def perpProj (v w : Pt) : Pt := w - (inner ℝ w v / inner ℝ v v) • v

def dihedral (c : Fin 4 → Pt) (i j k l : Fin 4) : ℝ :=
  InnerProductGeometry.angle (perpProj (c j - c i) (c k - c i)) (perpProj (c j - c i) (c l - c i))

def oth1 (i j : Fin 4) : Fin 4 :=
  if (0 : Fin 4) ≠ i ∧ (0 : Fin 4) ≠ j then 0 else if (1 : Fin 4) ≠ i ∧ (1 : Fin 4) ≠ j then 1 else 2

def oth2 (i j : Fin 4) : Fin 4 :=
  if (3 : Fin 4) ≠ i ∧ (3 : Fin 4) ≠ j then 3 else if (2 : Fin 4) ≠ i ∧ (2 : Fin 4) ≠ j then 2 else 1

def phiE (c : Fin 4 → Pt) (i j : Fin 4) : ℝ := dihedral c i j (oth1 i j) (oth2 i j)

def ell (c : Fin 4 → Pt) (i j : Fin 4) : ℝ :=
  (SphereGeom.arcMeasure (Metric.sphere (c i) 1 ∩ Metric.sphere (c j) 1 ∩ Kset c)).toReal /
    √(1 - q c i j / 4)

def isCommon (c : Fin 4 → Pt) (i j : Fin 4) : Prop := nRet c (oth1 i j) ≠ 0 ∧ nRet c (oth2 i j) ≠ 0

def Lapex (c : Fin 4 → Pt) (i j k : Fin 4) : ℝ :=
  (2 * q c i j * q c i k - q c i j ^ 2 - q c i k ^ 2 + q c j k * (q c i j + q c i k)) / Deltaf c i j k

def sigmaF (c : Fin 4 → Pt) (l : Fin 4) : ℝ :=
  gammaA c (faceVerts l).1 (faceVerts l).2.1 (faceVerts l).2.2 +
    gammaA c (faceVerts l).2.1 (faceVerts l).1 (faceVerts l).2.2 +
    gammaA c (faceVerts l).2.2 (faceVerts l).1 (faceVerts l).2.1

def apexTerm (c : Fin 4 → Pt) (i l : Fin 4) : Pt :=
  (Real.sign (det3 (c (oth1 i l) - c i) (c (oth2 i l) - c i) (c l - c i)) *
      Lapex c i (oth1 i l) (oth2 i l) / 4) • cross (c (oth1 i l) - c i) (c (oth2 i l) - c i)

def endTerm (c : Fin 4 → Pt) (i l : Fin 4) : Pt :=
  cross ((c (oth1 i l) - c i) - (c (oth2 i l) - c i)) (cross (c (oth1 i l) - c i) (c (oth2 i l) - c i))

def a0 (X Y : ℝ) : ℝ := 1 + X * Y / 2
def rX (X : ℝ) : ℝ := √(X * (1 - X / 4))
def b0 (X Y : ℝ) : ℝ := 2 * rX X * rX Y

def canonicalCenters (X Y s : ℝ) : Fin 4 → Pt :=
  ![0, WithLp.toLp 2 ![0, 0, 1], WithLp.toLp 2 ![rX X, 0, 1 - X / 2],
    WithLp.toLp 2 ![(a0 X Y - s) / (2 * rX X), √(Hpoly X Y s) / (2 * rX X), Y / 2]]

def faceCircRel (c : Fin 4 → Pt) (i j k : Fin 4) : Pt :=
  (q c i k * (q c i j - q c i k + q c j k) / Deltaf c i j k) • (c j - c i) +
  (q c i j * (q c i k - q c i j + q c j k) / Deltaf c i j k) • (c k - c i)

def Aface (c : Fin 4 → Pt) (l : Fin 4) : ℝ :=
  let i := (faceVerts l).1
  let j := (faceVerts l).2.1
  let k := (faceVerts l).2.2
  Deltaf c i j k * (q c i l - 2 * inner ℝ (c l - c i) (faceCircRel c i j k))

def triplePoint (c : Fin 4 → Pt) (i j k : Fin 4) (ε : ℝ) : Pt :=
  c i + faceCircRel c i j k +
    (ε * 2 * √(Qf c i j k) / Deltaf c i j k) • cross (c j - c i) (c k - c i)

def s0 (Y : ℝ) : ℝ := (1 - Y) ^ 2

def Bminus (Y s : ℝ) : ℝ :=
  (s - 2 * Y + 5 - 2 * √((3 - Y) * Qpoly 0 Y s 1 / Y)) / (4 - Y)

def Bplus (Y s : ℝ) : ℝ :=
  (s - 2 * Y + 5 + 2 * √((3 - Y) * Qpoly 0 Y s 1 / Y)) / (4 - Y)

def nearCounts (c : Fin 4 → Pt) : ℕ × ℕ := (nRet c 1, nRet c 0)

def wallSet : Set (ℝ × ℝ × ℝ) := {v |
  P4poly v.1 v.2.1 v.2.2 = 0 ∨ v.1 = v.2.1 ∨ v.2.2 = 1 ∨
  v.2.2 = s0 v.2.1 ∨ v.1 = 0 ∨ v.1 = 1 ∨ v.2.1 = 0 ∨ v.2.1 = 1 ∨
  ∃ l, Qpoly v.1 v.2.1 v.2.2 l = 0 ∨ Apoly v.1 v.2.1 v.2.2 l = 0}

structure PairArcDecomposition (c : Fin 4 → Pt) (i j : Fin 4) where
  U : Pt
  U_norm : ‖U‖ = 1
  U_perp : inner ℝ U (c j - c i) = 0
  intervals : List (ℝ × ℝ)
  bounds : ∀ ab ∈ intervals, 0 ≤ ab.1 ∧ ab.1 < ab.2 ∧ ab.2 ≤ 2 * π
  disjoint : intervals.Pairwise (fun ab cd => ab.2 ≤ cd.1 ∨ cd.2 ≤ ab.1)
  cover : ∀ t ∈ Set.Icc (0 : ℝ) (2 * π),
    ((1 / 2 : ℝ) • (c i + c j) +
      √(1 - q c i j / 4) • (Real.cos t • U + Real.sin t •
        cross ((1 / dist (c i) (c j)) • (c j - c i)) U)) ∈ Kset c ↔
      ∃ ab ∈ intervals, t ∈ Set.Icc ab.1 ab.2

def PairArcDecomposition.point {c : Fin 4 → Pt} {i j : Fin 4}
    (D : PairArcDecomposition c i j) (t : ℝ) : Pt :=
  (1 / 2 : ℝ) • (c i + c j) + √(1 - q c i j / 4) •
    (Real.cos t • D.U + Real.sin t • cross ((1 / dist (c i) (c j)) • (c j - c i)) D.U)

abbrev PairIndex := {p : Fin 4 × Fin 4 // p.1 < p.2}

def rawEndpointSum (c : Fin 4 → Pt)
    (D : ∀ e : PairIndex, PairArcDecomposition c e.1.1 e.1.2) : ℝ :=
  ∑ e : PairIndex, ((D e).intervals.map (fun ab =>
    inner ℝ (cross (c e.1.1) (c e.1.2)) ((D e).point ab.2 - (D e).point ab.1))).sum

def hcWeight (X : ℝ) : ℝ := (X + 2) / 4
def channelH2 (Y : ℝ) : ℝ := (Y + 2) / 4
def channelH3 (X Y s : ℝ) : ℝ := (X - Y - s - 1) / 4

def channelDensity (c : Fin 4 → Pt) (X h ε : ℝ) : ℝ :=
  hcWeight X * (h * vol c Finset.univ + (2 / 3) * h * pArea c 3 Finset.univ +
    ε * inner ℝ (c 1 - c 3) (pMoment c 3 Finset.univ) / 3)

def channelArcCoeff (c : Fin 4 → Pt) (X h ε : ℝ) (i j : Fin 4) : ℝ :=
  let d := dist (c i) (c j)
  let incident := i = 3 ∨ j = 3
  let other := if i = 3 then j else i
  hcWeight X * (h * (g d / 2 + if incident then d / 3 else 0) -
    if incident then ε * (1 - d ^ 2 / 4) * inner ℝ (c 1 - c 3) (c other - c 3) / (6 * d) else 0)

def scalarEndpointK (c : Fin 4 → Pt) (l : Fin 4) : ℝ :=
  let j := oth1 3 l
  let k := oth2 3 l
  ((q c 3 j - q c 3 k - q c j k) * inner ℝ (c 1 - c 3) (c j - c 3) -
   (q c 3 j - q c 3 k + q c j k) * inner ℝ (c 1 - c 3) (c k - c 3)) /
    (2 * Deltaf c 3 j k)

def channelCorner (c : Fin 4 → Pt) (X h : ℝ) : ℝ :=
  -hcWeight X * h / 3 * ∑ l, (nRet c l : ℝ) *
    (sigmaF c l + if l ≠ 3 then 2 * gammaA c 3 (oth1 3 l) (oth2 3 l) else 0)

def channelEndpoint (c : Fin 4 → Pt) (X Y s h ε : ℝ) : ℝ :=
  hcWeight X * h / 12 * ∑ l, (nRet c l : ℝ) * √(Qface c l) +
  ε * hcWeight X / 6 * ∑ l, (if l ≠ 3 then (nRet c l : ℝ) * √(Qface c l) * scalarEndpointK c l else 0) -
  (if 0 < P4poly X Y s then hcWeight X * h * √(Hpoly X Y s) / 12 else 0) +
  (if 0 < P4poly X Y s then ε * hcWeight X * √(Hpoly X Y s) * Lapex c 3 0 2 / 24 else 0)

abbrev Param := ℝ × ℝ × ℝ

def support : Set Param := {v | 0 < v.1 ∧ v.1 < 1 ∧ 0 < v.2.1 ∧ v.2.1 < 1 ∧ 0 < Hpoly v.1 v.2.1 v.2.2}

def pathMeasure : Measure Param := (volume.restrict support).withDensity
  (fun v => ENNReal.ofReal (π / √(Hpoly v.1 v.2.1 v.2.2)))

def nearDomain : Set Param := {v | v.2.2 < 1}
def nearSliver : Set Param := {v | v.2.2 < 1 ∧ P4poly v.1 v.2.1 v.2.2 < 0}
def nearBulk : Set Param := {v | v.2.2 < 1 ∧ 0 < P4poly v.1 v.2.1 v.2.2}
def weight (v : Param) : ℝ := (v.1 + v.2.1) / 2
def centers (v : Param) : Fin 4 → Pt := canonicalCenters v.1 v.2.1 v.2.2

def VfaceIntegral (l : Fin 4) : ℝ := -1 / 3 * ∫ v in nearDomain,
  weight v * (nRet (centers v) l : ℝ) * sigmaF (centers v) l ∂pathMeasure

def EfaceIntegral (l : Fin 4) : ℝ := 1 / 12 * ∫ v in nearDomain,
  weight v * (nRet (centers v) l : ℝ) * √(Qface (centers v) l) ∂pathMeasure

def Vadj : ℝ := VfaceIntegral 3
def Vnon : ℝ := VfaceIntegral 1
def Eadj : ℝ := EfaceIntegral 3
def Enon : ℝ := EfaceIntegral 1
def Ccap : ℝ := 8 * π / 3 * ∫ v in nearDomain, weight v ∂pathMeasure
def Dcap : ℝ := -1 / 12 * ∫ v in nearBulk, weight v * √(Hpoly v.1 v.2.1 v.2.2) ∂pathMeasure

def nearPairArc (i j : Fin 4) : ℝ := -1 / 2 * ∫ v in nearDomain,
  weight v * g (dist (centers v i) (centers v j)) * ell (centers v) i j ∂pathMeasure

def triangleSide (i j k : Fin 4) (l : Fin 4) : ℝ := -1 / 2 * ∫ v in nearDomain,
  weight v * g (dist (centers v i) (centers v j)) * (nRet (centers v) l : ℝ) *
    betaA (centers v) i j k ∂pathMeasure

def bulkSource (i j : Fin 4) : ℝ := 1 / 2 * ∫ v in nearBulk,
  weight v * g (dist (centers v i) (centers v j)) * phiE (centers v) i j ∂pathMeasure

def Ssliver : ℝ := π * g 1 * ∫ v in nearSliver, weight v ∂pathMeasure

def nearCorrection (i j : Fin 4) : ℝ := π * ∫ v in nearSliver,
  (if isCommon (centers v) i j then weight v * g (dist (centers v i) (centers v j)) else 0) ∂pathMeasure

def Kcap : ℝ := ∫ v in nearDomain, weight v * vol (centers v) Finset.univ ∂pathMeasure

def definitionLayer : Prop := True

end HardSphereB5.Lean.Geometry.PathCore
