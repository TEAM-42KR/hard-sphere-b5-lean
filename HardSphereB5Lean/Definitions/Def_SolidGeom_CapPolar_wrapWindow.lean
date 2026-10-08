import Mathlib
set_option autoImplicit false
noncomputable section
def SolidGeom.CapPolar.wrapWindow (T A B : ℝ) : Set ℝ :=
  Set.Ioo 0 T ∩ {φ | ∃ k : ℤ, A<φ+(k:ℝ)*T ∧ φ+(k:ℝ)*T<B}
def SolidGeom.CapPolar.clippedWindow (T A B : ℝ) : Set ℝ :=
  if B≤T then Set.Ioo A B else Set.Ioo A T ∪ Set.Ioo 0 (B-T)
