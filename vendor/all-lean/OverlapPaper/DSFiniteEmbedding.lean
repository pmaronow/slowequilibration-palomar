module

public import OverlapPaper.DSHilbertCoordinates
public import OverlapPaper.DSGramRotation

@[expose] public section

/-! Zero padding finite Gram vectors into the genuine Hilbert unit ball and
its compact coordinate model. All Gram entries are preserved exactly. -/
noncomputable section
open Set Filter Matrix WithLp MeasureTheory
open scoped Topology BigOperators RealInnerProductSpace lp MatrixOrder Matrix.Norms.L2Operator
namespace OverlapPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def finiteHilbertEmbedding {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : DSHilbert :=
  ∑ i : Fin n,lp.single 2 i.val (v i)

@[simp] theorem finiteHilbertEmbedding_apply_fin {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) : finiteHilbertEmbedding v i.val = v i := by
  simp only [finiteHilbertEmbedding,lp.coeFn_sum,Finset.sum_apply,lp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hj : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [hj.symm]
  · simp

theorem finiteHilbertEmbedding_apply_ge {n : ℕ} (v : EuclideanSpace ℝ (Fin n))
    {k : ℕ} (hk : n ≤ k) : finiteHilbertEmbedding v k = 0 := by
  simp only [finiteHilbertEmbedding,lp.coeFn_sum,Finset.sum_apply,lp.single_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi : k ≠ i.val := by omega
  simp [hi]

theorem finiteHilbertEmbedding_inner {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪finiteHilbertEmbedding v,finiteHilbertEmbedding w⟫ = ⟪v,w⟫ := by
  unfold finiteHilbertEmbedding
  rw [sum_inner]
  simp only [lp.inner_single_left]
  change (∑ i : Fin n,⟪v i,finiteHilbertEmbedding w i.val⟫)=⟪v,w⟫
  simp only [finiteHilbertEmbedding_apply_fin,PiLp.inner_apply]

theorem finiteHilbertEmbedding_norm {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ‖finiteHilbertEmbedding v‖ = ‖v‖ := by
  have hh := finiteHilbertEmbedding_inner v v
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg v,norm_nonneg (finiteHilbertEmbedding v)]

theorem continuous_finiteHilbertEmbedding {n : ℕ} :
    Continuous (finiteHilbertEmbedding : EuclideanSpace ℝ (Fin n) → DSHilbert) := by
  apply continuous_finsetSum
  intro i _
  exact (lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : ℕ => ℝ) 2 i.val).continuous.comp
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)

def finiteUnitCoordinates {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ ≤ 1) :
    DSCoordinateBall := hilbertUnitCoordinates ⟨finiteHilbertEmbedding v,by
      rw [finiteHilbertEmbedding_norm]
      exact hv⟩

@[simp] theorem coordinateVector_finiteUnitCoordinates {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ ≤ 1) :
    coordinateVector (finiteUnitCoordinates v hv)=finiteHilbertEmbedding v := by
  exact congrArg Subtype.val (coordinatesUnitHilbert_leftInverse
    ⟨finiteHilbertEmbedding v,by rw [finiteHilbertEmbedding_norm];exact hv⟩)

def rotatedGramCoordinates {n : ℕ} (R : GramArray)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (i : Fin n) : DSCoordinateBall :=
  finiteUnitCoordinates (rotatedGramVector (principalMatrix R.1 n) U i)
    (by rw [rotatedGramVector_norm _ (R.2 n) (fun j => by simp [principalMatrix,completeArray])])

theorem rotatedGramCoordinates_inner {n : ℕ} (R : GramArray)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (i j : Fin n) :
    ⟪coordinateVector (rotatedGramCoordinates R U i),
      coordinateVector (rotatedGramCoordinates R U j)⟫=completeArray R.1 i j := by
  simp only [rotatedGramCoordinates,coordinateVector_finiteUnitCoordinates]
  rw [finiteHilbertEmbedding_inner,rotatedGramVector_inner _ (R.2 n)]
  rfl

end OverlapPaper
