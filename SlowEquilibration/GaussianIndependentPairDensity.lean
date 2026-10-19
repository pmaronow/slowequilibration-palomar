-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPairBlockBounds
public import SlowEquilibration.GaussianPairDensity

/-! Pointwise density of the actual independent product observation. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function Module GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {E E' F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma independentPair_gram_det (A : E →L[ℝ] F) (B : E' →L[ℝ] F) :
    (gram (independentPair A B)).det=(gram A).det*(gram B).det := by
  classical
  let b:=stdOrthonormalBasis ℝ F
  have hmat : LinearMap.toMatrix (gramPairBasis b) (gramPairBasis b)
      (gram (independentPair A B)).toLinearMap=
      Matrix.fromBlocks
        (LinearMap.toMatrix b.toBasis b.toBasis (gram A).toLinearMap) 0 0
        (LinearMap.toMatrix b.toBasis b.toBasis (gram B).toLinearMap) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        rw [gramPairBasis_apply_left,gramPairBasis_repr_left,Matrix.fromBlocks_apply₁₁,
          LinearMap.toMatrix_apply]
        change b.repr (gram (independentPair A B) (WithLp.toLp 2 (b j,0))).fst i=b.repr (gram A (b j)) i
        rw [independentPair_gram_apply]
        rfl
      | inr j =>
        rw [gramPairBasis_apply_right,gramPairBasis_repr_left,Matrix.fromBlocks_apply₁₂]
        change b.repr (gram (independentPair A B) (WithLp.toLp 2 (0,b j))).fst i=0
        rw [independentPair_gram_apply]
        simp
    | inr i =>
      cases j with
      | inl j =>
        rw [gramPairBasis_apply_left,gramPairBasis_repr_right,Matrix.fromBlocks_apply₂₁]
        change b.repr (gram (independentPair A B) (WithLp.toLp 2 (b j,0))).snd i=0
        rw [independentPair_gram_apply]
        simp
      | inr j =>
        rw [gramPairBasis_apply_right,gramPairBasis_repr_right,Matrix.fromBlocks_apply₂₂,
          LinearMap.toMatrix_apply]
        change b.repr (gram (independentPair A B) (WithLp.toLp 2 (0,b j))).snd i=b.repr (gram B (b j)) i
        rw [independentPair_gram_apply]
        rfl
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix (gramPairBasis b),hmat,
    Matrix.det_fromBlocks_zero₂₁,LinearMap.det_toMatrix,LinearMap.det_toMatrix]

lemma independentPair_inverse_apply (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E' →L[ℝ] F) (hB : Surjective B) (w : WithLp 2 (F×F)) :
    (gram (independentPair A B)).inverse w=
      WithLp.toLp 2 ((gram A).inverse w.fst,(gram B).inverse w.snd) := by
  have h:=congrArg (fun T : WithLp 2 (F×F) →L[ℝ] WithLp 2 (F×F) =>
    T (WithLp.toLp 2 ((gram A).inverse w.fst,(gram B).inverse w.snd)))
    (gram_isInvertible (independentPair A B) (independentPair_surjective A B hA hB)).inverse_comp_self
  have hIA:=congrArg (fun T : F →L[ℝ] F => T w.fst) (gram_isInvertible A hA).self_comp_inverse
  have hIB:=congrArg (fun T : F →L[ℝ] F => T w.snd) (gram_isInvertible B hB).self_comp_inverse
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hIA hIB h
  rw [independentPair_gram_apply] at h
  simp only [WithLp.toLp_fst,WithLp.toLp_snd,hIA,hIB] at h
  exact h

/-- Exact actual ordinary product density at every score target, including
null conditioning targets; the identity is algebraic for the canonical pdf. -/
theorem realObservationDensity_independentPair (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E' →L[ℝ] F) (hB : Surjective B) (w : WithLp 2 (F×F)) :
    realObservationDensity (independentPair A B) w=
      realObservationDensity A w.fst*realObservationDensity B w.snd := by
  have hp:=independentPair_surjective A B hA hB
  have henergy : inner ℝ w ((gram (independentPair A B)).inverse w)=
      inner ℝ w.fst ((gram A).inverse w.fst)+inner ℝ w.snd ((gram B).inverse w.snd) := by
    rw [independentPair_inverse_apply A hA B hB,WithLp.prod_inner_apply]
    rfl
  apply Real.log_injOn_pos (realObservationDensity_pos _ hp _)
    (mul_pos (realObservationDensity_pos A hA _) (realObservationDensity_pos B hB _))
  rw [Real.log_mul (realObservationDensity_pos A hA _).ne' (realObservationDensity_pos B hB _).ne',
    log_realObservationDensity _ hp,log_realObservationDensity A hA,log_realObservationDensity B hB,
    log_normalizer_pair,independentPair_gram_det,
    Real.log_mul (gram_det_pos A hA).ne' (gram_det_pos B hB).ne',
    henergy]
  ring

/-- Equal actual covariances give equal canonical ordinary densities at every target. -/
theorem realObservationDensity_eq_of_gram (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E' →L[ℝ] F) (hB : Surjective B) (hGram : gram A=gram B) (w : F) :
    realObservationDensity A w=realObservationDensity B w := by
  apply Real.log_injOn_pos (realObservationDensity_pos A hA w) (realObservationDensity_pos B hB w)
  rw [log_realObservationDensity A hA w,log_realObservationDensity B hB w,hGram]

end
end SlowEquilibration.GaussianRegression
