import Mathlib
set_option autoImplicit false
open Matrix
open scoped Matrix
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000

theorem proof_HardSphereB5_SphericalCrofton_Aux_Coarea_incidence_chart_det5
    (A₀ A₁ B₀ B₁ c : Fin 3 → ℝ) (α₀ α₁ β₀ β₁ s t : ℝ) :
    Matrix.det
      ![![A₀ 0, A₀ 1, A₀ 2, -α₁ * s, 0],
        ![A₁ 0, A₁ 1, A₁ 2, α₀ * s, 0],
        ![B₀ 0, B₀ 1, B₀ 2, 0, -β₁ * t],
        ![B₁ 0, B₁ 1, B₁ 2, 0, β₀ * t],
        ![c 0, c 1, c 2, 0, 0]] =
      -(s * t) * Matrix.det ![α₀ • A₀ + α₁ • A₁, β₀ • B₀ + β₁ • B₁, c] := by
  classical
  let M : Matrix (Fin 5) (Fin 5) ℝ :=
    ![![A₀ 0, A₀ 1, A₀ 2, -α₁ * s, 0],
      ![A₁ 0, A₁ 1, A₁ 2, α₀ * s, 0],
      ![B₀ 0, B₀ 1, B₀ 2, 0, -β₁ * t],
      ![B₁ 0, B₁ 1, B₁ 2, 0, β₀ * t],
      ![c 0, c 1, c 2, 0, 0]]
  let N : Matrix (Fin 3) (Fin 3) ℝ :=
    ![α₀ • A₀ + α₁ • A₁, β₀ • B₀ + β₁ • B₁, c]
  let U : ℝ := α₀ ^ 2 + α₁ ^ 2
  let V : ℝ := β₀ ^ 2 + β₁ ^ 2
  change M.det = -(s * t) * N.det
  by_cases hU : U = 0
  · have ha₀ : α₀ = 0 := by dsimp [U] at hU; nlinarith [sq_nonneg α₁]
    have ha₁ : α₁ = 0 := by dsimp [U] at hU; nlinarith [sq_nonneg α₀]
    have hm : M.det = 0 := Matrix.det_eq_zero_of_column_eq_zero (3 : Fin 5) (by
      intro i; fin_cases i <;> simp [M, ha₀, ha₁])
    have hn : N.det = 0 := Matrix.det_eq_zero_of_row_eq_zero (0 : Fin 3) (by
      intro j; simp [N, ha₀, ha₁])
    simp [hm, hn]
  by_cases hV : V = 0
  · have hb₀ : β₀ = 0 := by dsimp [V] at hV; nlinarith [sq_nonneg β₁]
    have hb₁ : β₁ = 0 := by dsimp [V] at hV; nlinarith [sq_nonneg β₀]
    have hm : M.det = 0 := Matrix.det_eq_zero_of_column_eq_zero (4 : Fin 5) (by
      intro i; fin_cases i <;> simp [M, hb₀, hb₁])
    have hn : N.det = 0 := Matrix.det_eq_zero_of_row_eq_zero (1 : Fin 3) (by
      intro j; simp [N, hb₀, hb₁])
    simp [hm, hn]
  let La : Matrix (Fin 2) (Fin 2) ℝ := ![![α₀, α₁], ![-α₁, α₀]]
  let Lb : Matrix (Fin 2) (Fin 2) ℝ := ![![β₀, β₁], ![-β₁, β₀]]
  let L23 : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![β₀, β₁, 0], ![-β₁, β₀, 0], ![0, 0, 1]]
  let L : Matrix (Fin 5) (Fin 5) ℝ :=
    ![![α₀, α₁, 0, 0, 0], ![-α₁, α₀, 0, 0, 0],
      ![0, 0, β₀, β₁, 0], ![0, 0, -β₁, β₀, 0], ![0, 0, 0, 0, 1]]
  let e21 : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv
  let e23 : Fin 2 ⊕ Fin 3 ≃ Fin 5 := finSumFinEquiv
  let e32 : Fin 3 ⊕ Fin 2 ≃ Fin 5 := finSumFinEquiv
  have h23 : L23.submatrix e21 e21 = Matrix.fromBlocks Lb 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      rfl
  have d23 : L23.det = V := by
    calc
      L23.det = (L23.submatrix e21 e21).det := (Matrix.det_submatrix_equiv_self e21 L23).symm
      _ = (Matrix.fromBlocks Lb 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)).det := congrArg Matrix.det h23
      _ = V := by
        rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_fin_two]
        dsimp [Lb, V]
        ring
  have hL : L.submatrix e23 e23 = Matrix.fromBlocks La 0 0 L23 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      rfl
  have dL : L.det = U * V := by
    calc
      L.det = (L.submatrix e23 e23).det := (Matrix.det_submatrix_equiv_self e23 L).symm
      _ = (Matrix.fromBlocks La 0 0 L23).det := congrArg Matrix.det hL
      _ = U * V := by
        rw [Matrix.det_fromBlocks_zero₂₁, d23, Matrix.det_fin_two]
        dsimp [La, U]
        ring
  let q : Equiv.Perm (Fin 5) :=
    Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 3 4
  have dq : Equiv.Perm.sign q = -1 := by
    simp [q, map_mul, Equiv.Perm.sign_swap]
  let R : Matrix (Fin 5) (Fin 5) ℝ := (L * M).submatrix q id
  let C : Matrix (Fin 2) (Fin 3) ℝ :=
    ![-α₁ • A₀ + α₀ • A₁, -β₁ • B₀ + β₀ • B₁]
  let H : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![s * U, t * V]
  have hR : R.submatrix e32 e32 = Matrix.fromBlocks N 0 C H := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      dsimp [R, Matrix.submatrix, e32, finSumFinEquiv, q, Equiv.swap_apply_def,
        Matrix.fromBlocks, Matrix.diagonal, N, C, H]
    all_goals rw [Matrix.mul_apply]
    all_goals simp [Fin.sum_univ_succ, L, M, U, V, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    all_goals ring
  have dR : R.det = N.det * (s * U * (t * V)) := by
    calc
      R.det = (R.submatrix e32 e32).det := (Matrix.det_submatrix_equiv_self e32 R).symm
      _ = (Matrix.fromBlocks N 0 C H).det := congrArg Matrix.det hR
      _ = N.det * (s * U * (t * V)) := by
        rw [Matrix.det_fromBlocks_zero₁₂]
        simp [H, Matrix.det_diagonal, Fin.prod_univ_succ]
  have dRM : R.det = -(U * V) * M.det := by
    dsimp only [R]
    rw [Matrix.det_permute, dq, Matrix.det_mul, dL]
    simp
  apply mul_left_cancel₀ (mul_ne_zero hU hV)
  linear_combination dRM - dR

