-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalZeroGradientCornerValueMean

/-! Proper value-target version of the sharp zero-gradient physical corner
mean. This applies to pure models without observing a redundant radial mark. -/
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

lemma value_zero_gradient_lift {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e f : Fin m → Vector N) {δ : ℝ} (hδ : 0<δ)
    (hfull : CoerciveObservation
      (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)) δ)
    (h1 h2 : ℝ) :
    let j:=(hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin m))).toContinuousLinearEquiv
    lift (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f))
        (valuePairTarget N m h1 h2) =
      lift (residualPairValue c x y e f) (j (valuePairTarget N m h1 h2)).fst := by
  let D:=pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)
  let A:=pairGradient c x y e f
  let B:=valuePair c x y
  let w:=valuePairTarget N m h1 h2
  let j:=(hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin m))).toContinuousLinearEquiv
  let b:=(j w).fst
  have hD : Surjective D := observation_surjective D hδ hfull
  have hgroup : CoerciveObservation (pairHilbert B A) δ :=
    groupedValuePair_coercive c x y e f hfull
  have hA : Surjective A := observation_surjective A hδ (pair_snd_coercive B A hgroup)
  have hres : Surjective (B.comp (residual A)) := observation_surjective _ hδ
    (residual_coercivity A hA B hδ.le hgroup)
  have hC : Surjective (pairHilbert B A) := observation_surjective _ hδ hgroup
  have hchange : (j : _ →L[ℝ] _).comp D=pairHilbert B A :=
    (groupedValuePair_eq c x y e f).symm
  have hjw : j w=WithLp.toLp 2 (b,0) := rfl
  have hj := canonical_lift_target_equiv D hD j w
  rw [hchange,hjw,zero_gradient_joint_lift A hA B hres hC b] at hj
  exact hj.symm

/-- Literal proper-pure physical corner bound with constants before N and
all bounded value targets. The same value-only estimate holds for any mixture. -/
theorem source_value_corner_mean (μ : FiniteMixture) {Q M : ℝ} (hQ : 0<Q)
    (hd : 4≤μ.minDegree) (hM : 0≤M) :
    ∃ ρ C : ℝ,0<ρ ∧ 0<C ∧ ∀ (N m : ℕ) (_hN : 0<N)
      (x y u v : Vector N), ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ‖u‖=1 → ‖v‖=1 → inner ℝ u x=0 → inner ℝ v x=0 →
      ∀ (e f : Fin m → Vector N), Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) →
      ∀ h1 h2 : ℝ, |h1|≤M → |h2|≤M → |overlap x y|≤ρ →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      |flatJetCLM c 2 x ![u,v]
        (lift (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f))
          (valuePairTarget N m h1 h2))| ≤ C*|overlap x y|^(μ.minDegree-2) := by
  obtain ⟨ρ0,δ,hρ0,hδ,hall⟩:=uniform_value_pair_nondegenerate μ hQ hd
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let L:=profileBound c
  let C:=((4*L+42*L^2*(1/δ))*(1/δ)*(2*M))
  have hC : 0≤C := by positivity [profileBound_pos c]
  refine ⟨min ρ0 1,1+C,lt_min hρ0 (by norm_num),by positivity,?_⟩
  intro N m hN x y u v hx hy hu hv htanu htanv e f he hf htanx htany h1 h2 hh1 hh2 hr
  have hfull := (hall N m hN x y hx hy e f he hf htanx htany
    (hr.trans (min_le_left _ _))).1
  let A:=pairGradient c x y e f
  let B:=valuePair c x y
  let w:=valuePairTarget N m h1 h2
  let j:=(hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin m))).toContinuousLinearEquiv
  let b:=(j w).fst
  have hgroup := groupedValuePair_coercive c x y e f hfull
  have hgrad:=pair_snd_coercive B A hgroup
  have hA : Surjective A := observation_surjective A hδ hgrad
  have hres:=residual_coercivity A hA B hδ.le hgroup
  have hb : ‖b‖≤(2*M)*Real.sqrt (N:ℝ) := by
    have hfst:=WithLp.norm_fst_le _ (j w)
    change ‖b‖≤‖j w‖ at hfst
    have hjnorm : ‖j w‖=‖w‖ := (hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin m))).norm_map w
    rw [hjnorm] at hfst
    exact hfst.trans (valuePairTarget_norm_le N m hh1 hh2)
  have hbound:=residual_pair_value_corner_mean hN μ hQ.le hd x y u v hx hy hu hv htanu htanv
    e f he hf htanx htany b (by positivity : 0≤1/δ) (by positivity : 0≤2*M)
    hA (gram_inverse_norm_le A hδ hgrad) (gram_inverse_norm_le _ hδ hres) hb
    (hr.trans (min_le_right _ _))
  change |flatJetCLM c 2 x ![u,v]
    (lift (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f))
      (valuePairTarget N m h1 h2))|≤_
  rw [value_zero_gradient_lift c x y e f hδ hfull]
  exact hbound.trans (mul_le_mul_of_nonneg_right (by dsimp only [C,L];linarith)
    (pow_nonneg (abs_nonneg _) _))

end
end SlowEquilibration.PhysicalZeroGradientCorner
