module

public import OverlapPaper.DSGramEmpirical
public import OverlapPaper.DSCoordinateInner

@[expose] public section

/-! Actual finite-coordinate approximation error bounds for empirical Gram
sampling. The covariance identity proves monotonicity of aggregated squared
tails; individual signed coordinate tails need not be monotone. -/
noncomputable section
open Set Filter Matrix WithLp MeasureTheory
open scoped Topology BigOperators MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace OverlapPaper
set_option maxHeartbeats 800000

theorem finiteHilbertEmbedding_apply_zero_extension {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    finiteHilbertEmbedding v k=if h : k<n then v ⟨k,h⟩ else 0 := by
  split_ifs with hk
  · exact finiteHilbertEmbedding_apply_fin v ⟨k,hk⟩
  · exact finiteHilbertEmbedding_apply_ge v (by omega)

theorem sum_fin_zero_extension {n M : ℕ} (f : Fin n→ℝ) :
    (∑i : Fin M,if h : i.val<n then f ⟨i.val,h⟩ else 0)=
      ∑i ∈ Finset.univ.filter (fun i : Fin n => i.val<M),f i := by
  classical
  let g : Fin M→ℝ := fun i => if h : i.val<n then f ⟨i.val,h⟩ else 0
  calc
    _ = ∑i ∈ Finset.univ.filter (fun i : Fin M => i.val<n),g i := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val<n <;> simp [g,hi]
    _ = _ := by
      apply Finset.sum_bij (fun i hi => (⟨i.val,(Finset.mem_filter.mp hi).2⟩ : Fin n))
      · intro i hi
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        exact i.isLt
      · intro i hi j hj he
        exact Fin.ext (congrArg (fun k : Fin n => k.val) he)
      · intro j hj
        refine ⟨⟨j.val,(Finset.mem_filter.mp hj).2⟩,by simp [j.isLt],?_⟩
        rfl
      · intro i hi
        simp [g,(Finset.mem_filter.mp hi).2]

theorem finiteUnitCoordinates_prefix {n : ℕ} (v w : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖≤1) (hw : ‖w‖≤1) (M : ℕ) :
    coordinateInnerPrefix M (finiteUnitCoordinates v hv) (finiteUnitCoordinates w hw)=
      ∑k ∈ Finset.univ.filter (fun k : Fin n => k.val<M),v k*w k := by
  unfold coordinateInnerPrefix
  have he (i : Fin M) :
      ((finiteUnitCoordinates v hv).1 i.val : ℝ)*((finiteUnitCoordinates w hw).1 i.val : ℝ)=
      if h : i.val<n then v ⟨i.val,h⟩*w ⟨i.val,h⟩ else 0 := by
    change coordinateVector (finiteUnitCoordinates v hv) i.val*
      coordinateVector (finiteUnitCoordinates w hw) i.val=_
    rw [coordinateVector_finiteUnitCoordinates,coordinateVector_finiteUnitCoordinates,
      finiteHilbertEmbedding_apply_zero_extension,finiteHilbertEmbedding_apply_zero_extension]
    split_ifs <;> simp
  simp_rw [he]
  exact sum_fin_zero_extension (fun k : Fin n => v k*w k)

theorem finiteUnitCoordinates_inner_sub_prefix {n : ℕ} (v w : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖≤1) (hw : ‖w‖≤1) (M : ℕ) :
    ⟪coordinateVector (finiteUnitCoordinates v hv),coordinateVector (finiteUnitCoordinates w hw)⟫-
      coordinateInnerPrefix M (finiteUnitCoordinates v hv) (finiteUnitCoordinates w hw)=
      ∑k ∈ Finset.univ.filter (fun k : Fin n => M≤k.val),v k*w k := by
  rw [coordinateVector_finiteUnitCoordinates,coordinateVector_finiteUnitCoordinates,
    finiteHilbertEmbedding_inner,finiteUnitCoordinates_prefix]
  have he : ⟪v,w⟫=∑k : Fin n,v k*w k := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  have hs := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun k : Fin n => k.val<M) (fun k => v k*w k)
  simp only [not_lt] at hs
  linarith

theorem finite_empirical_squared_tail_mono {n : ℕ} (v : Fin n→EuclideanSpace ℝ (Fin n))
    (s t : Finset (Fin n)) (hst : s⊆t) :
    (n:ℝ)⁻¹^2*(∑i : Fin n,∑j : Fin n,(∑k∈s,v i k*v j k)^2) ≤
      (n:ℝ)⁻¹^2*(∑i : Fin n,∑j : Fin n,(∑k∈t,v i k*v j k)^2) := by
  rw [finite_empirical_tail_identity,finite_empirical_tail_identity]
  calc
    _ ≤ ∑k∈s,∑l∈t,(finiteEmpiricalCovariance v k l)^2 := by
      apply Finset.sum_le_sum
      intro k _
      exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem empiricalGramCoordinates_inner_prefix_error (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε)
    (R : GramArray) (M : ℕ) :
    (n:ℝ)⁻¹^2*(∑i : Fin n,∑j : Fin n,
      (completeArray R.1 i.val j.val-coordinateInnerPrefix M
        (empiricalGramCoordinates n hn ε hε R i) (empiricalGramCoordinates n hn ε hε R j))^2) ≤
      1/((M+1:ℕ):ℝ)+ε := by
  have he (i j : Fin n) : completeArray R.1 i.val j.val-coordinateInnerPrefix M
      (empiricalGramCoordinates n hn ε hε R i) (empiricalGramCoordinates n hn ε hε R j)=
      ∑k ∈ Finset.univ.filter (fun k : Fin n => M≤k.val),
        rotatedGramVector (principalMatrix R.1 n) (measurableGramRotation n hn ε hε R) i k*
        rotatedGramVector (principalMatrix R.1 n) (measurableGramRotation n hn ε hε R) j k := by
    rw [←empiricalGramCoordinates_inner n hn ε hε R i j]
    have hb (l : Fin n) : ‖rotatedGramVector (principalMatrix R.1 n)
        (measurableGramRotation n hn ε hε R) l‖≤1 := by
      rw [rotatedGramVector_norm _ (R.2 n) (fun k => by simp [principalMatrix,completeArray])]
    simpa only [empiricalGramCoordinates,rotatedGramCoordinates] using
      finiteUnitCoordinates_inner_sub_prefix _ _ (hb i) (hb j) M
  simp_rw [he]
  exact (Classical.choose_spec (exists_measurable_Gram_rotation n hn ε hε)).2 R M

end OverlapPaper
