module

public import OverlapPaper.DSGramRotation

@[expose] public section

/-! A deterministic sorted spectral rotation and its actual empirical tail
bound. No measurability of this eigenbasis choice is asserted: a separate
countable approximation will provide the measurable rotations. -/
noncomputable section
open Set Filter Matrix WithLp
open scoped Topology MatrixOrder Matrix.Norms.L2Operator BigOperators RealInnerProductSpace
namespace OverlapPaper
set_option maxHeartbeats 800000

def gramSpectralPermutation (n : ℕ) : Fin n ≃ Fin n :=
  (finCongr (Fintype.card_fin n).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))))

def permuteUnitaryColumns {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℝ) (r : Fin n ≃ Fin n) :
    Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨Matrix.of (fun i j => U i (r j)),by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    change (star (U : Matrix (Fin n) (Fin n) ℝ)*(U : Matrix (Fin n) (Fin n) ℝ)) (r i) (r j) =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j
    rw [Unitary.star_mul_self_of_mem U.2]
    simp only [Matrix.one_apply,r.injective.eq_iff]⟩

theorem permuteUnitaryColumns_conjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (r : Fin n ≃ Fin n) (i j : Fin n) :
    (star (permuteUnitaryColumns U r : Matrix (Fin n) (Fin n) ℝ)*A*
      (permuteUnitaryColumns U r : Matrix (Fin n) (Fin n) ℝ)) i j =
      (star (U : Matrix (Fin n) (Fin n) ℝ)*A*(U : Matrix (Fin n) (Fin n) ℝ)) (r i) (r j) := rfl

def sortedGramUnitary {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    Matrix.unitaryGroup (Fin n) ℝ :=
  permuteUnitaryColumns hA.eigenvectorUnitary (gramSpectralPermutation n)

theorem sortedGramUnitary_conjugate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    star (sortedGramUnitary hA : Matrix (Fin n) (Fin n) ℝ)*A*
      (sortedGramUnitary hA : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal (orderedGramEigenvalue hA) := by
  have hs := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at hs
  ext i j
  rw [sortedGramUnitary,permuteUnitaryColumns_conjugate,hs]
  simp only [Matrix.diagonal_apply,Function.comp_apply,RCLike.ofReal_real_eq_id,id_eq,
    (gramSpectralPermutation n).injective.eq_iff]
  congr 1
  unfold gramSpectralPermutation orderedGramEigenvalue Matrix.IsHermitian.eigenvalues
  simp only [Equiv.trans_apply,finCongr_apply,Equiv.symm_apply_apply]

theorem sortedGramVector_covariance {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) :
    finiteEmpiricalCovariance (rotatedGramVector A (sortedGramUnitary hA.isHermitian)) =
      Matrix.diagonal (normalizedGramSpectrum hA.isHermitian) := by
  rw [rotatedGramVector_covariance A hA,sortedGramUnitary_conjugate]
  ext k l
  simp [Matrix.diagonal_apply,normalizedGramSpectrum]

theorem sortedGramVector_tail {n : ℕ} (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hdiag : ∀ i,A i i = 1) (M : ℕ) :
    (n:ℝ)⁻¹^2*(∑ i : Fin n,∑ j : Fin n,
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => M ≤ k.val),
        rotatedGramVector A (sortedGramUnitary hA.isHermitian) i k*
        rotatedGramVector A (sortedGramUnitary hA.isHermitian) j k)^2) ≤
      1/((M+1:ℕ):ℝ) := by
  rw [finite_empirical_tail_identity,sortedGramVector_covariance hA]
  have he : (∑ k ∈ Finset.univ.filter (fun k : Fin n => M ≤ k.val),
      ∑ l ∈ Finset.univ.filter (fun l : Fin n => M ≤ l.val),
        (Matrix.diagonal (normalizedGramSpectrum hA.isHermitian) k l)^2) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => M ≤ k.val),
        (normalizedGramSpectrum hA.isHermitian k)^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [Matrix.diagonal_apply,hk]
  rw [he]
  exact normalizedGramSpectrum_tail hn hA hdiag M

end OverlapPaper
