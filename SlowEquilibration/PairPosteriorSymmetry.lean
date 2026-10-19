-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ObservationTargetEquiv
public import SlowEquilibration.PurePairConditionalDeterminantMoments

/-! The two actual posterior Hessians share one genuine disorder law.
Swapping the observation pair preserves the canonical posterior at every
physical target, and both determinant moment bounds hold under that law. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity ObservationTargetEquiv
open SphericalTwoPointCovariance PairObservationTargets IntrinsicHessianLaw
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma coefficientKernel_pair_swap {N P : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    (A : EuclideanDisorder N P →L[ℝ] F) (B : EuclideanDisorder N P →L[ℝ] G)
    (hP : Surjective (pairHilbert A B)) (w : WithLp 2 (F×G)) :
    coefficientKernel (pairHilbert B A) (WithLp.toLp 2 (w.snd,w.fst))=
      coefficientKernel (pairHilbert A B) w := by
  let e:=(LinearIsometryEquiv.withLpProdComm 2 ℝ F G).toContinuousLinearEquiv
  have he : pairHilbert B A=(e : WithLp 2 (F×G) →L[ℝ] WithLp 2 (G×F)).comp (pairHilbert A B) := by
    ext z
    rfl
  rw [he]
  exact coefficientKernel_target_equiv _ hP e w

/-- Both actual Hessian determinants have all moments under one literal
mixed pair posterior. No independence between their determinants is assumed. -/
theorem mixed_pair_both_moments (μ : FiniteMixture) {Q M g : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hdeg : 4 ≤ μ.minDegree) (hM : 0 < M) (hg : 0 < g) :
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 1 ≤ K ∧ ∀ (n : ℕ) (x y : Vector (n+2))
      (hx : ‖x‖^2=(n+2 : ℕ)) (hy : ‖y‖^2=(n+2 : ℕ))
      (h1 k1 h2 k2 : ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M →
      |overlap x y| ≤ ρ0 → 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ k1 →
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ k2 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleMixedObservation c x (tangentFrame x hx))
        (singleMixedObservation c y (tangentFrame y hy))
      let w:=mixedPairTarget (n+2) (n+1) h1 k1 h2 k2
      Surjective A ∧ PosteriorMoments (coefficientKernel A w)
        (ConditionedDeterminantMoments.intrinsicDet μ Q x) K ∧
      PosteriorMoments (coefficientKernel A w)
        (ConditionedDeterminantMoments.intrinsicDet μ Q y) K := by
  obtain ⟨ρ0,K,hρ0,hK,hall⟩:=mixed_pair_moments μ hQ hnp hdeg hM hg
  refine ⟨ρ0,K,hρ0,hK,?_⟩
  intro n x y hx hy h1 k1 h2 k2 hh1 hk1 hh2 hk2 hr hgap1 hgap2
  have hxmom:=hall n x y hx hy h1 k1 h2 k2 hh1 hk1 hh2 hk2 hr hgap1
  have hr' : |overlap y x| ≤ ρ0 := by rwa [overlap_comm]
  have hymom:=hall n y x hy hx h2 k2 h1 k1 hh2 hk2 hh1 hk1 hr' hgap2
  have hswap:=coefficientKernel_pair_swap _ _ hxmom.1
    (mixedPairTarget (n+2) (n+1) h1 k1 h2 k2)
  change coefficientKernel (pairHilbert
    (singleMixedObservation (centerCoefficients (mixtureCoefficients μ) Q) y (tangentFrame y hy))
    (singleMixedObservation (centerCoefficients (mixtureCoefficients μ) Q) x (tangentFrame x hx)))
    (mixedPairTarget (n+2) (n+1) h2 k2 h1 k1)=_ at hswap
  dsimp only at hymom
  rw [hswap] at hymom
  exact ⟨hxmom.1,hxmom.2,hymom.2⟩

/-- Proper pure pair conditioning gives both Hessian moment bounds under
its actual common value/tangent posterior and the proved radial shifts p*h. -/
theorem pure_pair_both_moments (p : ℕ) (hp : 4 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q M g : ℝ} (hQ : 0 < Q) (hM : 0 < M) (hg : 0 < g) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 1 ≤ K ∧ ∀ (n : ℕ) (x y : Vector (n+2))
      (hx : ‖x‖^2=(n+2 : ℕ)) (hy : ‖y‖^2=(n+2 : ℕ))
      (h1 h2 : ℝ),|h1| ≤ M → |h2| ≤ M → |overlap x y| ≤ ρ0 →
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*h1 →
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*h2 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleValueObservation c x (tangentFrame x hx))
        (singleValueObservation c y (tangentFrame y hy))
      let w:=valuePairTarget (n+2) (n+1) h1 h2
      Surjective A ∧ PosteriorMoments (coefficientKernel A w)
        (ConditionedDeterminantMoments.intrinsicDet μ Q x) K ∧
      PosteriorMoments (coefficientKernel A w)
        (ConditionedDeterminantMoments.intrinsicDet μ Q y) K := by
  dsimp only
  obtain ⟨ρ0,K,hρ0,hK,hall⟩:=pure_pair_moments p hp alpha halpha hQ hM hg
  refine ⟨ρ0,K,hρ0,hK,?_⟩
  intro n x y hx hy h1 h2 hh1 hh2 hr hgap1 hgap2
  have hxmom:=hall n x y hx hy h1 h2 hh1 hh2 hr hgap1
  have hr' : |overlap y x| ≤ ρ0 := by rwa [overlap_comm]
  have hymom:=hall n y x hy hx h2 h1 hh2 hh1 hr' hgap2
  have hswap:=coefficientKernel_pair_swap _ _ hxmom.1 (valuePairTarget (n+2) (n+1) h1 h2)
  change coefficientKernel (pairHilbert
    (singleValueObservation (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p (by omega) alpha halpha)) Q) y (tangentFrame y hy))
    (singleValueObservation (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p (by omega) alpha halpha)) Q) x (tangentFrame x hx)))
    (valuePairTarget (n+2) (n+1) h2 h1)=_ at hswap
  dsimp only at hymom
  rw [hswap] at hymom
  exact ⟨hxmom.1,hxmom.2,hymom.2⟩

end
end SlowEquilibration.PairConditionalDeterminantMoments
