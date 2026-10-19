-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPairDensitySharp
public import SlowEquilibration.PairGradientHilbertSchmidt
public import SlowEquilibration.ObservationCrossBlockOrders
public import SlowEquilibration.PairGradientNondegeneracy

/-! Genuine dimension-uniform pair tangent-gradient density factorization.
The actual cross-block square sum preserves its rank-one contribution,
giving the source sharp error m |overlap|^(2d−2)+|overlap|^(2d−4). -/
@[expose] public section
namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity PairObservationCrossCovariance
open SphericalTwoPointCovariance NormalizedObservationCoercivity PairObservationNormBounds
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

/-- Constants are chosen before the ambient dimension and complete tangent
frames. The ratio involves the actual two-gradient density and its actual
one-point marginal densities, all at the literal zero target. -/
theorem uniform_pair_gradient_density_sharp (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 0 < K ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=gradientCLM c x e
      let B:=gradientCLM c y f
      Surjective (pairHilbert A B) ∧
        |Real.log (realObservationDensity (pairHilbert A B) 0 /
          (realObservationDensity A 0*realObservationDensity B 0))| ≤
            K*((m:ℝ)*|overlap x y|^(2*(μ.minDegree-1))+|overlap x y|^(2*(μ.minDegree-2))) := by
  obtain ⟨r,hr,hall⟩:=uniform_pair_gradient_surjective μ hQ hdeg
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let L:=profileBound c
  let a:=Q*μ.xi1 Q
  have hL : 0 < L := profileBound_pos c
  have ha : 0 < a := mul_pos hQ (mixture_xi1_pos μ hQ)
  let ρ0:=min r (min 1 (a/(4*L)))
  let K:=2*L^2/a^2
  have hρ0 : 0 < ρ0 := lt_min hr (lt_min (by norm_num) (by positivity))
  have hK : 0 < K := by dsimp [K];positivity
  refine ⟨ρ0,K,hρ0,hK,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ
  have hρr : |overlap x y| ≤ r := hρ.trans (min_le_left _ _)
  have hρ1 : |overlap x y| ≤ 1 :=
    (hρ.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hρa : |overlap x y| ≤ a/(4*L) :=
    (hρ.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hc:=centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hdegree : ∀ p,c p≠0 → μ.minDegree ≤ p.val.val := by
    intro p hp
    have hcoeff : μ.coeff p.val.val≠0 := by intro hz;apply hp;simp [c,centerCoefficients,mixtureCoefficients,hz]
    exact (μ.degree_bounds (Finsupp.mem_support_iff.mpr hcoeff)).1
  have horder:=gradient_cross_order hN c hc (by omega : 2 ≤ μ.minDegree) hdegree
    x y hx hy e f he hf hρ1
  have hpow : |overlap x y|^(μ.minDegree-2) ≤ |overlap x y| := by
    simpa only [pow_one] using pow_le_pow_of_le_one (abs_nonneg _) hρ1 (show 1 ≤ μ.minDegree-2 by omega)
  have hcross : ‖(gradientCLM c x e).comp (gradientCLM c y f).adjoint‖ ≤ a/2 := by
    apply horder.trans
    have hh:=(le_div_iff₀ (by positivity : 0 < 4*L)).mp hρa
    have hp:=mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2*L)
    nlinarith
  have hAx : gram (gradientCLM c x e)=a • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) := by
    rw [gradient_gram hN c hc x hx e he htanx,firstCovariance_center,firstCovariance_mixture]
  have hBy : gram (gradientCLM c y f)=a • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) := by
    rw [gradient_gram hN c hc y hy f hf htany,firstCovariance_center,firstCovariance_mixture]
  have hA:=observation_surjective _ ha (gradient_coercivity hN μ hQ x hx e he htanx)
  have hB:=observation_surjective _ ha (gradient_coercivity hN μ hQ y hy f hf htany)
  have hPair:=hall N m hN x y hx hy e f he hf htanx htany hρr
  refine ⟨hPair,?_⟩
  have hbound:=isotropic_pair_density_ratio_bound_sharp (EuclideanSpace.basisFun (Fin m) ℝ)
    _ _ hA hB hPair ha hAx hBy hcross
  have hHS:=gradient_cross_hilbertSchmidt_order hN c hc (by omega : 2 ≤ μ.minDegree) hdegree
    x y hx hy e f he hf hρ1
  apply hbound.trans
  calc
    _ ≤ (1/a^2)*(2*L^2*((m:ℝ)*|overlap x y|^(2*(μ.minDegree-1))+
        |overlap x y|^(2*(μ.minDegree-2)))) := mul_le_mul_of_nonneg_left hHS (by positivity)
    _ = _ := by dsimp only [K];ring

end
end SlowEquilibration.PairObservationSmallOverlap
