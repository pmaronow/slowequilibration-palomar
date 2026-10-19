module

public import OverlapPaper.DSSortedRotation
public import OverlapPaper.DSMeasurableChoice

@[expose] public section

/-! Actual measurable finite Gram rotations with a uniform empirical tail
certificate. The sorted eigenbasis is used only to prove feasibility; the
chosen rotation comes from a fixed countable dense sequence. -/
noncomputable section
open Set Filter Matrix MeasureTheory WithLp
open scoped Topology MatrixOrder Matrix.Norms.L2Operator BigOperators RealInnerProductSpace
namespace OverlapPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def gramCovarianceTailEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => M ≤ k.val),
    ∑ l ∈ Finset.univ.filter (fun l : Fin n => M ≤ l.val),
      (((n:ℝ)⁻¹ • (star (U : Matrix (Fin n) (Fin n) ℝ)*A*
        (U : Matrix (Fin n) (Fin n) ℝ))) k l)^2

theorem gramCovarianceTailEnergy_eq_pair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (U : Matrix.unitaryGroup (Fin n) ℝ) (M : ℕ) :
    gramCovarianceTailEnergy A U M = (n:ℝ)⁻¹^2*(∑ i : Fin n,∑ j : Fin n,
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => M ≤ k.val),
        rotatedGramVector A U i k*rotatedGramVector A U j k)^2) := by
  rw [finite_empirical_tail_identity,rotatedGramVector_covariance A hA U]
  rfl

def gramRotationCost {n : ℕ} (R : GramArray) (U : Matrix.unitaryGroup (Fin n) ℝ) : ℝ :=
  ∑ M : Fin (n+1),max 0 (gramCovarianceTailEnergy (principalMatrix R.1 n) U M.val-
    1/((M.val+1:ℕ):ℝ))

theorem continuous_gramRotationCost {n : ℕ} :
    Continuous (fun p : GramArray×Matrix.unitaryGroup (Fin n) ℝ => gramRotationCost p.1 p.2) := by
  unfold gramRotationCost gramCovarianceTailEnergy
  apply continuous_finsetSum
  intro M _
  apply continuous_const.max
  apply Continuous.sub _ continuous_const
  apply continuous_finsetSum
  intro k _
  apply continuous_finsetSum
  intro l _
  apply Continuous.pow
  have hA : Continuous (fun p : GramArray×Matrix.unitaryGroup (Fin n) ℝ => principalMatrix p.1.1 n) :=
    (continuous_principalMatrix n).comp (continuous_subtype_val.comp continuous_fst)
  have hU : Continuous (fun p : GramArray×Matrix.unitaryGroup (Fin n) ℝ =>
      (p.2 : Matrix (Fin n) (Fin n) ℝ)) := continuous_subtype_val.comp continuous_snd
  exact ((continuous_apply l).comp (continuous_apply k)).comp
    ((hU.star.mul hA).mul hU |>.const_smul (n:ℝ)⁻¹)

theorem gramRotationCost_sorted {n : ℕ} (hn : 0 < n) (R : GramArray) :
    gramRotationCost R (sortedGramUnitary (R.2 n).isHermitian) = 0 := by
  apply Finset.sum_eq_zero
  intro M _
  apply max_eq_left
  apply sub_nonpos.mpr
  rw [gramCovarianceTailEnergy_eq_pair _ (R.2 n)]
  exact sortedGramVector_tail hn (R.2 n) (fun i => by simp [principalMatrix,completeArray]) M.val

theorem exists_measurable_Gram_rotation (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : GramArray → Matrix.unitaryGroup (Fin n) ℝ,Measurable U ∧ ∀ R M,
      (n:ℝ)⁻¹^2*(∑ i : Fin n,∑ j : Fin n,
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => M ≤ k.val),
          rotatedGramVector (principalMatrix R.1 n) (U R) i k*
          rotatedGramVector (principalMatrix R.1 n) (U R) j k)^2) ≤
        1/((M+1:ℕ):ℝ)+ε := by
  have hcU (U : Matrix.unitaryGroup (Fin n) ℝ) :
      Measurable (fun R : GramArray => gramRotationCost R U) :=
    ((continuous_gramRotationCost (n := n)).comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : GramArray => U)))).measurable
  have hcR (R : GramArray) : Continuous (fun U : Matrix.unitaryGroup (Fin n) ℝ => gramRotationCost (n := n) R U) := by
    apply Continuous.comp (f := fun U : Matrix.unitaryGroup (Fin n) ℝ => (R,U)) (continuous_gramRotationCost (n := n))
    exact continuous_const.prodMk continuous_id
  obtain ⟨U,hU,hcost⟩ := exists_measurable_approximate_choice (X := GramArray) (K := Matrix.unitaryGroup (Fin n) ℝ) gramRotationCost (fun _ : GramArray => (0:ℝ))
    hcU measurable_const hcR ε hε (fun R =>
      ⟨sortedGramUnitary (R.2 n).isHermitian,(gramRotationCost_sorted hn R).le⟩)
  refine ⟨U,hU,fun R M => ?_⟩
  rw [←gramCovarianceTailEnergy_eq_pair _ (R.2 n)]
  by_cases hM : M ≤ n
  · let m : Fin (n+1) := ⟨M,by omega⟩
    have hm : max 0 (gramCovarianceTailEnergy (principalMatrix R.1 n) (U R) M-
        1/((M+1:ℕ):ℝ)) ≤ gramRotationCost R (U R) := by
      simpa only [gramRotationCost,m] using Finset.single_le_sum
        (f := fun i : Fin (n+1) => max 0 (gramCovarianceTailEnergy (principalMatrix R.1 n) (U R) i.val-
          1/((i.val+1:ℕ):ℝ)))
        (fun i _ => le_max_left (0:ℝ) _) (Finset.mem_univ m)
    have hraw := le_max_right (0:ℝ) (gramCovarianceTailEnergy (principalMatrix R.1 n) (U R) M-
      1/((M+1:ℕ):ℝ))
    have hh := hcost R
    simp only [zero_add] at hh
    linarith
  · have hemp : Finset.univ.filter (fun k : Fin n => M ≤ k.val) = ∅ := by
      ext k
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
      omega
    simp only [gramCovarianceTailEnergy,hemp,Finset.sum_empty]
    positivity

end OverlapPaper
