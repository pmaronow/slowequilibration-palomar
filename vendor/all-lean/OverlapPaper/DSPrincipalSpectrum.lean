module

public import OverlapPaper.DSSpectralTail

@[expose] public section

/-! The dimension-independent tail estimate applies to the actual ordered
eigenvalues of every finite principal Gram matrix. -/
noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators
namespace OverlapPaper
set_option maxHeartbeats 800000

def orderedGramEigenvalue {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (i : Fin n) : ℝ :=
  hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

theorem orderedGramEigenvalue_antitone {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : Antitone (orderedGramEigenvalue hA) := by
  intro i j hij
  apply hA.eigenvalues₀_antitone
  exact hij

theorem orderedGramEigenvalue_sum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : ∑ i,orderedGramEigenvalue hA i = A.trace := by
  rw [hA.trace_eq_sum_eigenvalues]
  unfold orderedGramEigenvalue Matrix.IsHermitian.eigenvalues
  calc
    _ = ∑ i : Fin (Fintype.card (Fin n)),hA.eigenvalues₀ i :=
      (Equiv.sum_comp (finCongr (Fintype.card_fin n).symm) hA.eigenvalues₀)
    _ = _ := (Equiv.sum_comp
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm hA.eigenvalues₀).symm

theorem orderedGramEigenvalue_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i : Fin n) : 0 ≤ orderedGramEigenvalue hA.isHermitian i := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have hh := hA.eigenvalues_nonneg (e (Fin.cast (Fintype.card_fin n).symm i))
  simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply,orderedGramEigenvalue] using hh

def normalizedGramSpectrum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (i : Fin n) : ℝ := (n:ℝ)⁻¹*orderedGramEigenvalue hA i

theorem normalizedGramSpectrum_tail {n : ℕ} (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hdiag : ∀ i,A i i = 1) (M : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => M ≤ i.val),
      (normalizedGramSpectrum hA.isHermitian i)^2 ≤ 1/((M+1:ℕ):ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  apply antitone_nonneg_spectral_tail
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (orderedGramEigenvalue_antitone hA.isHermitian hij)
      (inv_nonneg.mpr hnR.le)
  · intro i
    exact mul_nonneg (inv_nonneg.mpr hnR.le) (orderedGramEigenvalue_nonneg hA i)
  · unfold normalizedGramSpectrum
    rw [←Finset.mul_sum,orderedGramEigenvalue_sum]
    have ht : A.trace = (n:ℝ) := by simp [Matrix.trace,hdiag]
    rw [ht,inv_mul_cancel₀ hnR.ne']

end OverlapPaper
