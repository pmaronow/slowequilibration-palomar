-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairProjectedJetBounds

/-! Explicit Gaussian tails for the actual unit tensor-jet supremum after
coefficient contraction and a deterministic conditional-mean shift. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set
open PureTensorJetFeatures PureTensorJetBounds PureTensorJetConcentration
open SphericalAging.FiniteModel GaussianNormConcentration
open scoped ENNReal
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma sourceProjectedUnitJetEnvelope_lipschitz {ι:Type*} [Fintype ι]
    {N p j:ℕ} (hN:0<N)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p)) (hT:‖T‖ ≤ 1) :
    LipschitzWith ((p:ℝ)^j).toNNReal (sourceProjectedUnitJetEnvelope N p j T):=by
  apply LipschitzWith.of_dist_le_mul
  intro g z
  have hh:=(unitEnvelope_lipschitz (p:=p) (j:=j) hN).dist_le_mul (T g) (T z)
  rw [Real.coe_toNNReal _ (by positivity)] at hh
  have hd:dist (T g) (T z) ≤ dist g z:=by
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact (T.le_opNorm _).trans (by nlinarith [norm_nonneg (g-z)])
  change dist (unitJetEnvelope N p j (WithLp.ofLp (T g)))
    (unitJetEnvelope N p j (WithLp.ofLp (T z))) ≤ _
  rw [Real.coe_toNNReal _ (by positivity)]
  exact hh.trans (mul_le_mul_of_nonneg_left hd (by positivity))

theorem sourceProjectedUnitJetEnvelope_centered_tail {ι:Type*} [Fintype ι]
    {N p j:ℕ} (hN:0<N)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p)) (hT:‖T‖ ≤ 1)
    {s:ℝ} (hs:0 ≤ s) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {g|(∫ z,sourceProjectedUnitJetEnvelope N p j T z ∂SYK.standardGaussianMeasureOnEuclidean ι)+s ≤
        sourceProjectedUnitJetEnvelope N p j T g} ≤ Real.exp (-s^2/(2*((p:ℝ)^j)^2)):=
  centered_lipschitz_upper_tail _ (by positivity)
    (sourceProjectedUnitJetEnvelope_lipschitz hN T hT) hs

theorem sourceProjectedUnitJetEnvelope_tail {ι:Type*} [Fintype ι]
    {N p j:ℕ} (hN:0<N) (hp:1 ≤ p)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p)) (hT:‖T‖ ≤ 1) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {g|(2*((j:ℝ)+2)*(p:ℝ)^j*Real.sqrt p+1)*Real.sqrt N ≤
        sourceProjectedUnitJetEnvelope N p j T g} ≤ Real.exp (-(N:ℝ)/(2*((p:ℝ)^j)^2)):=by
  have hm:=sourceProjectedUnitJetEnvelope_mean_bound (j:=j) hN hp T hT
  have ht:=sourceProjectedUnitJetEnvelope_centered_tail (j:=j) hN T hT (s:=Real.sqrt N) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (Nat.cast_nonneg N)] at ht
  refine (measureReal_mono (fun g hg=>?_)).trans ht
  change (∫ z,sourceProjectedUnitJetEnvelope N p j T z ∂SYK.standardGaussianMeasureOnEuclidean ι)+Real.sqrt N ≤ _
  change (2*((j:ℝ)+2)*(p:ℝ)^j*Real.sqrt p+1)*Real.sqrt N ≤ _ at hg
  nlinarith

lemma sourceProjectedUnitJetEnvelope_shift_le {ι:Type*} [Fintype ι]
    {N p j:ℕ} (hN:0<N)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p))
    (g:EuclideanSpace ℝ ι) (m:EuclideanSpace ℝ (TensorIndex N p)) :
    unitJetEnvelope N p j (WithLp.ofLp (T g+m)) ≤
      sourceProjectedUnitJetEnvelope N p j T g+(p:ℝ)^j*‖m‖:=by
  have hh:=(unitEnvelope_lipschitz (p:=p) (j:=j) hN).dist_le_mul (T g+m) (T g)
  rw [Real.dist_eq,Real.coe_toNNReal _ (by positivity),dist_eq_norm,add_sub_cancel_left] at hh
  change _ ≤ unitJetEnvelope N p j (WithLp.ofLp (T g))+(p:ℝ)^j*‖m‖
  linarith [le_abs_self (unitJetEnvelope N p j (WithLp.ofLp (T g+m))-
    unitJetEnvelope N p j (WithLp.ofLp (T g)))]

theorem sourceProjectedAffineUnitJetEnvelope_tail {ι:Type*} [Fintype ι]
    {N p j:ℕ} (hN:0<N) (hp:1 ≤ p)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p)) (hT:‖T‖ ≤ 1)
    (m:EuclideanSpace ℝ (TensorIndex N p)) {K:ℝ} (hm:‖m‖ ≤ K*Real.sqrt N) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {g|(2*((j:ℝ)+2)*(p:ℝ)^j*Real.sqrt p+1+(p:ℝ)^j*K)*Real.sqrt N ≤
        unitJetEnvelope N p j (WithLp.ofLp (T g+m))} ≤
      Real.exp (-(N:ℝ)/(2*((p:ℝ)^j)^2)):=by
  refine (measureReal_mono (fun g hg=>?_)).trans (sourceProjectedUnitJetEnvelope_tail (j:=j) hN hp T hT)
  have hs:=sourceProjectedUnitJetEnvelope_shift_le (j:=j) hN T g m
  have hshift:=mul_le_mul_of_nonneg_left hm (show 0 ≤ (p:ℝ)^j by positivity)
  change (2*((j:ℝ)+2)*(p:ℝ)^j*Real.sqrt p+1)*Real.sqrt N ≤ _
  change (2*((j:ℝ)+2)*(p:ℝ)^j*Real.sqrt p+1+(p:ℝ)^j*K)*Real.sqrt N ≤ _ at hg
  nlinarith

end
end SlowEquilibration.PairConditionalDeterminantMoments
