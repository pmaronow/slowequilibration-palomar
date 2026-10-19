-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NormalizedObservationCoercivity
public import SlowEquilibration.PairObservationTargets

/-! The actual normalized one-point observation lift has coefficient norm
O(sqrt N), uniformly over physical marks and tangent frames. Coercivity and
all mean bounds are derived from the actual finite mixture. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function
open SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity NormalizedPairObservations
open NormalizedObservationCoercivity PairObservationTargets
open scoped RealInnerProductSpace
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma coercive_lift_norm_bound {E F:Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A:E→L[ℝ]F) {δ:ℝ} (hδ:0<δ) (hA:CoerciveObservation A δ) (w:F) :
    ‖lift A w‖ ≤ ‖w‖/Real.sqrt δ:=by
  let u:=(gram A).inverse w
  have he:gram A u=w:=by
    exact congrArg (fun T:F→L[ℝ]F=>T w) (gram_isInvertible A (observation_surjective A hδ hA)).self_comp_inverse
  have hEq:‖lift A w‖^2=inner ℝ u w:=by
    change ‖A.adjoint u‖^2=inner ℝ u w
    rw [←gram_inner A u,he]
  have hu:‖u‖ ≤ (1/δ)*‖w‖:=
    ((gram A).inverse.le_opNorm w).trans (mul_le_mul_of_nonneg_right (gram_inverse_norm_le A hδ hA) (norm_nonneg w))
  have hSq:‖lift A w‖^2 ≤ (‖w‖/Real.sqrt δ)^2:=by
    rw [div_pow,Real.sq_sqrt hδ.le,hEq]
    calc
      _ ≤ ‖u‖*‖w‖:=real_inner_le_norm u w
      _ ≤ ((1/δ)*‖w‖)*‖w‖:=mul_le_mul_of_nonneg_right hu (norm_nonneg w)
      _ = _:=by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hSq

theorem source_mixed_one_point_coefficient_mean_bound (μ:FiniteMixture) {Q M:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hM:0 ≤ M) :
    ∃ K:ℝ,0<K ∧ ∀ (N m:ℕ),0<N → ∀ (x:Vector N),‖x‖^2=(N:ℝ) →
      ∀ (e:Fin m→Vector N),Orthonormal ℝ e → (∀ i,inner ℝ (e i) x=0) →
      ∀ (h k:ℝ),|h| ≤ M → |k| ≤ M →
      ‖lift (singleMixedObservation (centerCoefficients (mixtureCoefficients μ) Q) x e)
        (mixedPointTarget N m h k)‖ ≤ K*Real.sqrt N:=by
  obtain ⟨δ,hδ,hcoerc⟩:=uniform_mixed_coercivity μ hQ hnp
  let K:=2*M/Real.sqrt δ+1
  have hK:0<K:=by unfold K;positivity
  refine ⟨K,hK,?_⟩
  intro N m hN x hx e he htan h k hh hk
  have hb:=coercive_lift_norm_bound
    (singleMixedObservation (centerCoefficients (mixtureCoefficients μ) Q) x e)
      hδ (hcoerc N m hN x hx e he htan) (mixedPointTarget N m h k)
  calc
    _ ≤ ‖mixedPointTarget N m h k‖/Real.sqrt δ:=hb
    _ ≤ (2*M*Real.sqrt N)/Real.sqrt δ:=by
      exact div_le_div_of_nonneg_right (mixedPointTarget_norm_le N m hh hk) (Real.sqrt_nonneg _)
    _ ≤ K*Real.sqrt N:=by
      unfold K
      rw [show (2*M*Real.sqrt (N:ℝ))/Real.sqrt δ=(2*M/Real.sqrt δ)*Real.sqrt N by ring]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

lemma source_value_point_target_norm_le (N m:ℕ) {M h:ℝ} (hh:|h| ≤ M) :
    ‖valuePointTarget N m h‖ ≤ M*Real.sqrt N:=by
  have hp:=hilbertPair_norm_le_sum (valuePointTarget N m h)
  change ‖valuePointTarget N m h‖ ≤ |Real.sqrt (N:ℝ)*h|+‖(0:EuclideanSpace ℝ (Fin m))‖ at hp
  rw [norm_zero,add_zero,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] at hp
  exact hp.trans ((mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _))

theorem source_value_one_point_coefficient_mean_bound (μ:FiniteMixture) {Q M:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) :
    ∃ K:ℝ,0<K ∧ ∀ (N m:ℕ),0<N → ∀ (x:Vector N),‖x‖^2=(N:ℝ) →
      ∀ (e:Fin m→Vector N),Orthonormal ℝ e → (∀ i,inner ℝ (e i) x=0) →
      ∀ h:ℝ,|h| ≤ M →
      ‖lift (singleValueObservation (centerCoefficients (mixtureCoefficients μ) Q) x e)
        (valuePointTarget N m h)‖ ≤ K*Real.sqrt N:=by
  obtain ⟨δ,hδ,hcoerc⟩:=uniform_value_coercivity μ hQ
  let K:=M/Real.sqrt δ+1
  have hK:0<K:=by unfold K;positivity
  refine ⟨K,hK,?_⟩
  intro N m hN x hx e he htan h hh
  have hb:=coercive_lift_norm_bound
    (singleValueObservation (centerCoefficients (mixtureCoefficients μ) Q) x e)
      hδ (hcoerc N m hN x hx e he htan) (valuePointTarget N m h)
  calc
    _ ≤ ‖valuePointTarget N m h‖/Real.sqrt δ:=hb
    _ ≤ (M*Real.sqrt N)/Real.sqrt δ:=by
      exact div_le_div_of_nonneg_right (source_value_point_target_norm_le N m hh) (Real.sqrt_nonneg _)
    _ ≤ K*Real.sqrt N:=by
      unfold K
      rw [show (M*Real.sqrt (N:ℝ))/Real.sqrt δ=(M/Real.sqrt δ)*Real.sqrt N by ring]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

end
end SlowEquilibration.PairConditionalDeterminantMoments
