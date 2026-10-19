-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOESignedAbsoluteTransfer
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

/-! # The genuine bordered determinant identity

No invertibility of the principal minor is imposed. Polynomial lifting removes
the temporary nonzero-determinant condition in the cancellation argument.
-/

namespace SlowEquilibration.GOEBorderedDeterminant

noncomputable section
open Matrix Polynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def border (a : R) (r c : ι → R) (B : Matrix ι ι R) : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R :=
  Matrix.fromBlocks (fun _ _ : Unit => a) (fun _ i => r i) (fun i _ => c i) B

lemma border_det_of_ne_zero [IsDomain R] (a : R) (r c : ι → R) (B : Matrix ι ι R)
    (hB : B.det ≠ 0) :
    (border a r c B).det = a * B.det - r ⬝ᵥ (B.adjugate *ᵥ c) := by
  let A : Matrix Unit Unit R := fun _ _ => a
  let row : Matrix Unit ι R := fun _ i => r i
  let col : Matrix ι Unit R := fun i _ => c i
  let T : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R :=
    fromBlocks (B.det • (1 : Matrix Unit Unit R)) 0 (-(B.adjugate * col)) 1
  have hmul : border a r c B * T =
      fromBlocks (B.det • A - row * B.adjugate * col) row 0 B := by
    dsimp only [border, T]
    rw [fromBlocks_multiply]
    congr 1
    · simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc,
        sub_eq_add_neg]
      rfl
    · simp only [Matrix.mul_zero, Matrix.mul_one, zero_add]
      rfl
    · simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc,
        Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
      change B.det • col + -(B.det • col) = 0
      exact add_neg_cancel _
    · simp only [Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hT : T.det = B.det := by
    dsimp only [T]
    rw [det_fromBlocks_zero₁₂, det_smul, det_one, det_one]
    simp
  have htop : (B.det • A - row * B.adjugate * col).det =
      a * B.det - r ⬝ᵥ (B.adjugate *ᵥ c) := by
    rw [Matrix.det_unique]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, A, row, col,
      Matrix.mul_apply, dotProduct, mulVec]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc, mul_comm B.det]
  have hdet := congrArg Matrix.det hmul
  rw [det_mul, hT, det_fromBlocks_zero₂₁, htop] at hdet
  exact mul_right_cancel₀ hB hdet

/-- The exact adjugate border identity, including singular principal minors. -/
theorem border_det (a : R) (r c : ι → R) (B : Matrix ι ι R) :
    (border a r c B).det = a * B.det - r ⬝ᵥ (B.adjugate *ᵥ c) := by
  -- The lifting ring may have zero divisors, so use the universal integral
  -- polynomial matrix first, exactly as in Mathlib's adjugate identities.
  let M := Matrix.mvPolynomialX (Unit ⊕ ι) (Unit ⊕ ι) ℤ
  let a' := M (Sum.inl ()) (Sum.inl ())
  let r' : ι → MvPolynomial ((Unit ⊕ ι) × (Unit ⊕ ι)) ℤ := fun i => M (Sum.inl ()) (Sum.inr i)
  let c' : ι → MvPolynomial ((Unit ⊕ ι) × (Unit ⊕ ι)) ℤ := fun i => M (Sum.inr i) (Sum.inl ())
  let D' : Matrix ι ι (MvPolynomial ((Unit ⊕ ι) × (Unit ⊕ ι)) ℤ) :=
    M.submatrix Sum.inr Sum.inr
  have hD' : D'.det ≠ 0 := by
    intro hz
    let ev : MvPolynomial ((Unit ⊕ ι) × (Unit ⊕ ι)) ℤ →ₐ[ℤ] ℤ := MvPolynomial.aeval (fun p : (Unit ⊕ ι) × (Unit ⊕ ι) =>
      (1 : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℤ) p.1 p.2)
    have h := congrArg ev hz
    rw [map_zero, AlgHom.map_det] at h
    have hid : ev.mapMatrix D' = (1 : Matrix ι ι ℤ) := by
      ext i j
      simp [D', M, ev, Matrix.mvPolynomialX, Matrix.one_apply]
    rw [hid, det_one] at h
    exact one_ne_zero h
  have hpoly := border_det_of_ne_zero a' r' c' D' hD'
  let ev : MvPolynomial ((Unit ⊕ ι) × (Unit ⊕ ι)) ℤ →ₐ[ℤ] R := MvPolynomial.aeval (fun p : (Unit ⊕ ι) × (Unit ⊕ ι) =>
    border a r c B p.1 p.2)
  have h := congrArg ev hpoly
  simp only [map_sub, map_mul, AlgHom.map_det] at h
  have hborder : ev.mapMatrix (border a' r' c' D') = border a r c B := by
    ext i j
    cases i <;> cases j <;> simp [border, a', r', c', D', M, ev, Matrix.mvPolynomialX]
  have hminor : ev.mapMatrix D' = B := by
    ext i j
    simp [D', M, ev, Matrix.mvPolynomialX, border]
  rw [hborder, hminor] at h
  have ha : ev a' = a := by simp [a', M, ev, border]
  have hr (i : ι) : ev (r' i) = r i := by simp [r', M, ev, Matrix.mvPolynomialX, border]
  have hc (i : ι) : ev (c' i) = c i := by simp [c', M, ev, Matrix.mvPolynomialX, border]
  have hadj (i j : ι) : ev (D'.adjugate i j) = B.adjugate i j := by
    have hh := AlgHom.map_adjugate ev D'
    rw [hminor] at hh
    exact congrFun (congrFun hh i) j
  simp only [dotProduct, mulVec, map_sum, map_mul, ha, hr, hc, hadj] at h
  exact h

def zeroSuccEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv x := by cases x with | inl u => cases u; rfl | inr i => rfl
  right_inv i := by cases i using Fin.cases <;> rfl

/-- The same singular-minor identity in literal Fin successor coordinates. -/
theorem det_successor_border {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det -
      (fun i : Fin n => A 0 i.succ) ⬝ᵥ
        ((A.submatrix Fin.succ Fin.succ).adjugate *ᵥ (fun i => A i.succ 0)) := by
  have h := border_det (A 0 0) (fun i : Fin n => A 0 i.succ)
    (fun i => A i.succ 0) (A.submatrix Fin.succ Fin.succ)
  have he : A.submatrix (zeroSuccEquiv n) (zeroSuccEquiv n) =
      border (A 0 0) (fun i : Fin n => A 0 i.succ)
        (fun i => A i.succ 0) (A.submatrix Fin.succ Fin.succ) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [← he, Matrix.det_submatrix_equiv_self] at h
  exact h

end
end SlowEquilibration.GOEBorderedDeterminant
