import HardSphereB5Lean.Proofs.Proof_SphereGeom_Aux_Crofton_encard_monotone_iUnion
import Mathlib
set_option autoImplicit false
open scoped Classical

theorem SphereGeom.Aux.Crofton.encard_monotone_iUnion :
    ∀ {α : Type} (s : ℕ → Set α) (hs : Monotone s), (⋃ n, s n).encard = ⨆ n, (s n).encard :=
  @proof_SphereGeom_Aux_Crofton_encard_monotone_iUnion
