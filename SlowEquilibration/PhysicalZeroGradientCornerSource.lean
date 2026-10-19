-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalZeroGradientCornerMean

/-! Literal physical two-point Gaussian corner mean on the simultaneous
zero tangent-gradient fiber. All covariance nondegeneracy estimates are
proved internally; constants are chosen before dimension and physical marks. -/
@[expose] public section
namespace SlowEquilibration.PhysicalZeroGradientCorner
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open PairObservationNormBounds PairObservationTargets PairObservationSmallOverlap
open GaussianRegression GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma mixed_zero_gradient_lift {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) {δ : ℝ} (hδ : 0<δ)
    (hfull : CoerciveObservation
      (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)) δ)
    (h1 k1 h2 k2 : ℝ) :
    lift (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f))
        (mixedPairTarget N m h1 k1 h2 k2) =
      lift (residualPairScore c x y e f)
        (pairScoreProjection m (mixedPairTarget N m h1 k1 h2 k2)) := by
  let D:=pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)
  let A:=pairGradient c x y e f
  let B:=scorePair c x y
  let w:=mixedPairTarget N m h1 k1 h2 k2
  let b:=pairScoreProjection m w
  let j:=(mixedGroupingEquiv m).toContinuousLinearEquiv
  have hD : Surjective D := observation_surjective D hδ hfull
  have hgroup : CoerciveObservation (pairHilbert B A) δ :=
    groupedMixedPair_coercive c x y e f hfull
  have hA : Surjective A := observation_surjective A hδ (pair_snd_coercive B A hgroup)
  have hres : Surjective (B.comp (residual A)) := observation_surjective _ hδ
    (residual_coercivity A hA B hδ.le hgroup)
  have hC : Surjective (pairHilbert B A) := observation_surjective _ hδ hgroup
  have hchange : (j : MixedPairSpace m →L[ℝ] GroupedMixedPairSpace m).comp D=
      pairHilbert B A := groupedMixedPair_eq c x y e f |>.symm
  have hjw : j w=WithLp.toLp 2 (b,0) := rfl
  have hj := canonical_lift_target_equiv D hD j w
  rw [hchange,hjw,zero_gradient_joint_lift A hA B hres hC b] at hj
  exact hj.symm

/-- Sharp source corner-mean estimate for the original mixed/proper-pure
branch with nonredundant mixed marks. It concerns the actual full observation
lift, with literal normalized energy/radial targets and both gradients zero. -/
theorem source_mixed_corner_mean (μ : FiniteMixture) {Q M : ℝ} (hQ : 0<Q)
    (hnp : μ.minDegree<μ.maxDegree) (hd : 4≤μ.minDegree) (hM : 0≤M) :
    ∃ ρ C : ℝ,0<ρ ∧ 0<C ∧ ∀ (N m : ℕ) (_hN : 0<N)
      (x y u v : Vector N), ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ‖u‖=1 → ‖v‖=1 → inner ℝ u x=0 → inner ℝ v x=0 →
      ∀ (e f : Fin m → Vector N), Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) →
      ∀ h1 k1 h2 k2 : ℝ, |h1|≤M → |k1|≤M → |h2|≤M → |k2|≤M →
      |overlap x y|≤ρ →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      |flatJetCLM c 2 x ![u,v]
        (lift (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f))
          (mixedPairTarget N m h1 k1 h2 k2))| ≤ C*|overlap x y|^(μ.minDegree-2) := by
  obtain ⟨ρ0,δ,hρ0,hδ,hall⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hd
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let L:=profileBound c
  let C:=((4*L+42*L^2*(1/δ))*(1/δ)*(4*M))
  have hC : 0≤C := by positivity [profileBound_pos c]
  refine ⟨min ρ0 1,1+C,lt_min hρ0 (by norm_num),by positivity,?_⟩
  intro N m hN x y u v hx hy hu hv htanu htanv e f he hf htanx htany
    h1 k1 h2 k2 hh1 hk1 hh2 hk2 hr
  have hfull := (hall N m hN x y hx hy e f he hf htanx htany
    (hr.trans (min_le_left _ _))).1
  let A:=pairGradient c x y e f
  let B:=scorePair c x y
  let w:=mixedPairTarget N m h1 k1 h2 k2
  let b:=pairScoreProjection m w
  have hgroup := groupedMixedPair_coercive c x y e f hfull
  have hgrad:=pair_snd_coercive B A hgroup
  have hA : Surjective A := observation_surjective A hδ hgrad
  have hres:=residual_coercivity A hA B hδ.le hgroup
  have hb : ‖b‖≤(4*M)*Real.sqrt (N:ℝ) := by
    have hfst:=WithLp.norm_fst_le _ (mixedGrouping m w)
    change ‖b‖≤‖mixedGrouping m w‖ at hfst
    rw [mixedGrouping_norm] at hfst
    exact hfst.trans (mixedPairTarget_norm_le N m hh1 hk1 hh2 hk2)
  have hbound:=residual_pair_score_corner_mean hN μ hQ.le hd x y u v hx hy hu hv htanu htanv
    e f he hf htanx htany b (by positivity : 0≤1/δ) (by positivity : 0≤4*M)
    hA (gram_inverse_norm_le A hδ hgrad) (gram_inverse_norm_le _ hδ hres) hb
    (hr.trans (min_le_right _ _))
  change |flatJetCLM c 2 x ![u,v]
    (lift (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f))
      (mixedPairTarget N m h1 k1 h2 k2))|≤_
  rw [mixed_zero_gradient_lift c x y e f hδ hfull]
  exact hbound.trans (mul_le_mul_of_nonneg_right (by dsimp only [C,L];linarith)
    (pow_nonneg (abs_nonneg _) _))

end
end SlowEquilibration.PhysicalZeroGradientCorner
