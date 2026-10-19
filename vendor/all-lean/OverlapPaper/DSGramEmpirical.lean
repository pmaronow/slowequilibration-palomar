module

public import OverlapPaper.DSMeasurableRotation
public import OverlapPaper.DSFiniteEmpirical

@[expose] public section

/-! Genuine measurable empirical directing measures of finite Gram arrays.
The approximate spectral rotations alter coordinates but preserve Gram entries. -/
noncomputable section
open Set Filter Matrix WithLp MeasureTheory
open scoped Topology BigOperators MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace OverlapPaper
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 64

theorem continuous_rotatedPrincipalGramVector {n : ℕ} (i : Fin n) :
    Continuous (fun p : GramArray×Matrix.unitaryGroup (Fin n) ℝ =>
      rotatedGramVector (principalMatrix p.1.1 n) p.2 i) := by
  have hA : Continuous (fun p : GramArray×Matrix.unitaryGroup (Fin n) ℝ => principalMatrix p.1.1 n) :=
    (continuous_principalMatrix n).comp (continuous_subtype_val.comp continuous_fst)
  have hS : Continuous (fun p : GramArray×Matrix.unitaryGroup (Fin n) ℝ => CFC.sqrt (principalMatrix p.1.1 n)) := by
    have hc : ContinuousOn (CFC.sqrt : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
        {A | A.PosSemidef} := by
      simpa only [Matrix.nonneg_iff_posSemidef] using (CFC.continuousOn_sqrt (A := Matrix (Fin n) (Fin n) ℝ))
    exact hc.comp_continuous hA (fun p => p.1.2 n)
  have hU : Continuous (fun p : GramArray×Matrix.unitaryGroup (Fin n) ℝ =>
      (p.2 : Matrix (Fin n) (Fin n) ℝ)) := continuous_subtype_val.comp continuous_snd
  have hcol : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ =>
      (toLp 2 (fun j => A j i) : EuclideanSpace ℝ (Fin n))) := by fun_prop
  exact hcol.comp (hU.star.mul hS)

theorem continuous_rotatedGramCoordinates {n : ℕ} (i : Fin n) :
    Continuous (fun p : GramArray×Matrix.unitaryGroup (Fin n) ℝ => rotatedGramCoordinates p.1 p.2 i) := by
  have hH := (continuous_finiteHilbertEmbedding (n := n)).comp (continuous_rotatedPrincipalGramVector (n := n) i)
  have hball : Continuous (fun p : GramArray×Matrix.unitaryGroup (Fin n) ℝ =>
      (⟨finiteHilbertEmbedding (rotatedGramVector (principalMatrix p.1.1 n) p.2 i),by
        rw [finiteHilbertEmbedding_norm,rotatedGramVector_norm _ (p.1.2 n)
          (fun j => by simp [principalMatrix,completeArray])]
        ⟩ : DSNormBall)) := hH.subtype_mk _
  exact continuous_hilbertUnitCoordinates.comp hball

def measurableGramRotation (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    GramArray → Matrix.unitaryGroup (Fin n) ℝ :=
  Classical.choose (exists_measurable_Gram_rotation n hn ε hε)

theorem measurable_measurableGramRotation (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    Measurable (measurableGramRotation n hn ε hε) :=
  (Classical.choose_spec (exists_measurable_Gram_rotation n hn ε hε)).1

def empiricalGramCoordinates (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε)
    (R : GramArray) (i : Fin n) : DSCoordinateBall :=
  rotatedGramCoordinates R (measurableGramRotation n hn ε hε R) i

theorem measurable_empiricalGramCoordinates (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) (i : Fin n) :
    Measurable (fun R => empiricalGramCoordinates n hn ε hε R i) := by
  unfold empiricalGramCoordinates
  apply Measurable.comp (f := fun R : GramArray => (R,measurableGramRotation n hn ε hε R))
    ((continuous_rotatedGramCoordinates (n := n) i).measurable)
  exact measurable_id.prodMk (measurable_measurableGramRotation n hn ε hε)

def empiricalGramProbability (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε)
    (R : GramArray) : ProbabilityMeasure DSCoordinateBall :=
  finiteEmpiricalProbability hn (empiricalGramCoordinates n hn ε hε R)

theorem measurable_empiricalGramProbability (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    Measurable (empiricalGramProbability n hn ε hε) :=
  measurable_finiteEmpiricalProbability hn _ (fun i => measurable_empiricalGramCoordinates n hn ε hε i)

theorem empiricalGramCoordinates_inner (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε)
    (R : GramArray) (i j : Fin n) :
    ⟪coordinateVector (empiricalGramCoordinates n hn ε hε R i),
      coordinateVector (empiricalGramCoordinates n hn ε hε R j)⟫=completeArray R.1 i j :=
  rotatedGramCoordinates_inner R _ i j

theorem empiricalGramCoordinates_pair_tail (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε)
    (R : GramArray) (M : ℕ) :
    (n:ℝ)⁻¹^2*(∑ i : Fin n,∑ j : Fin n,
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => M ≤ k.val),
        coordinateVector (empiricalGramCoordinates n hn ε hε R i) k.val*
        coordinateVector (empiricalGramCoordinates n hn ε hε R j) k.val)^2) ≤
      1/((M+1:ℕ):ℝ)+ε := by
  simp only [empiricalGramCoordinates,rotatedGramCoordinates,coordinateVector_finiteUnitCoordinates,
    finiteHilbertEmbedding_apply_fin]
  exact (Classical.choose_spec (exists_measurable_Gram_rotation n hn ε hε)).2 R M

end OverlapPaper
