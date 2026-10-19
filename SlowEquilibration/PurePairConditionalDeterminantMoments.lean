-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairConditionalDeterminantMoments

/-! Genuine determinant moments under proper pure pair conditioning. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity HessianObservationCovariance
open SphericalTwoPointCovariance PairObservationNormBounds PairObservationTargets
open SphericalHessianTraceCovariance IntrinsicHessianLaw PairHessianMean PairObservationSmallOverlap
open SphericalConditionalMatrices
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Pure pair conditioning uses only values and tangent gradients. Its
actual radial shift is p*h1, and no independent radial target is admitted. -/
theorem pure_pair_moments (p : ℕ) (hp : 4 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q M g : ℝ} (hQ : 0 < Q) (hM : 0 < M) (hg : 0 < g) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 1 ≤ K ∧ ∀ (n : ℕ) (x y : Vector (n+2))
      (hx : ‖x‖^2=(n+2 : ℕ)) (hy : ‖y‖^2=(n+2 : ℕ))
      (h1 h2 : ℝ),|h1| ≤ M → |h2| ≤ M → |overlap x y| ≤ ρ0 →
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*h1 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairHilbert (singleValueObservation c x (tangentFrame x hx))
        (singleValueObservation c y (tangentFrame y hy))
      let w:=valuePairTarget (n+2) (n+1) h1 h2
      Surjective A ∧ PosteriorMoments (coefficientKernel A w)
        (ConditionedDeterminantMoments.intrinsicDet μ Q x) K := by
  dsimp only
  let μ:=FiniteMixture.pure p (by omega) alpha halpha
  have hdeg : 4 ≤ μ.minDegree := by
    have hdegree : μ.minDegree=p := by
      simp [μ,FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p halpha.ne']
    rw [hdegree]
    exact hp
  obtain ⟨ρbase,δ,hρbase,hδ,hpair⟩:=uniform_value_pair_nondegenerate μ hQ hdeg
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let C:=7*profileBound c*(2*M)/δ
  have hC : 0 < C := by dsimp [C];positivity [profileBound_pos c]
  let ρ0:=min ρbase (min 1 (g/(4*C)))
  have hρ0 : 0 < ρ0 := lt_min hρbase (lt_min (by norm_num) (by positivity))
  obtain ⟨K0,hK0,hall⟩:=GaussianMatrixMomentLaw.normalized_moments_all_dimensions
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hg
  refine ⟨ρ0,K0,hρ0,hK0,?_⟩
  intro n x y hx hy h1 h2 hh1 hh2 hr hk
  let e:=tangentFrame x hx
  let f:=tangentFrame y hy
  let A:=pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)
  let w:=valuePairTarget (n+2) (n+1) h1 h2
  have hd:=hpair (n+2) (n+1) (by omega) x y hx hy e f
    (tangentFrame_orthonormal x hx) (tangentFrame_orthonormal y hy)
    (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) (hr.trans (min_le_left _ _))
  have hr1 : |overlap x y| ≤ 1 := hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrC : C*|overlap x y| ≤ g/4 := by
    have hh:=hr.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh':=(le_div_iff₀ (by positivity : 0 < 4*C)).mp hh
    nlinarith
  have hmean : ‖OAI.CriticalSK.gaussianMatrixCLM (hessianGaussianCLM c x e (lift A w))‖ ≤ g/4 :=
    (value_lift_hessian_opNorm (by omega) c
      (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le)
      (center_degree_four hdeg Q) x y hx hy e f
      (tangentFrame_orthonormal x hx) (tangentFrame_orthonormal y hy)
      (tangentFrame_tangent x hx) w hδ (by positivity) hd.2.2
      (valuePairTarget_norm_le (n+2) (n+1) hh1 hh2) hr1).trans hrC
  have hrad : ∀ᵐ J ∂coefficientKernel A w,jet c 1 x (fun _ => x) J=(n+2 : ℕ)*((p:ℝ)*h1) :=
    pure_pair_first_radial_ae (by omega) p (by omega) alpha halpha Q x y e f h1 h2 hd.2.1
  let B:=hessianGaussianCLM c x e
  let ν:=GaussianRegressionCovariance.centeredLaw A B
  let D:=B (lift A w)
  have hvar (L : GOEAsymptotics.GaussianMatrix (n+1)) (hL : ∀ i j,L i j=L j i) :
      Var[fun W => Matrix.trace (SymmetricGaussianCovariance.entries W*SymmetricGaussianCovariance.entries L);ν] ≤
        (2*(Q^2*μ.xi2 Q)/(n+2 : ℕ))*Matrix.trace (SymmetricGaussianCovariance.entries L*SymmetricGaussianCovariance.entries L) := by
    have hv:=conditioned_hessian_trace_variance_bound A hd.2.1 (by omega) c
      (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) x
      (r := 1) (by simpa using hx) e (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx) L hL
    dsimp only [c] at hv
    simpa only [secondCovariance_center,secondCovariance_mixture] using hv
  have hbulk:=hall (n+2) n (by omega) ν (GaussianRegressionCovariance.centeredLaw_mean A B)
    (centered_hessian_symmetric_ae A c x e) hvar D (hessianGaussianCLM_symmetric c x e _) hmean ((p:ℝ)*h1) hk
  have hD:=actual_intrinsicDet_conditional_hasLaw μ Q x hx A w ((p:ℝ)*h1) hrad
  have hresult:=conditional_moments_of_matrix_law ν D ((p:ℝ)*h1) (g/2) _ hbulk
    (ConditionedDeterminantMoments.intrinsicDet μ Q x) hD
  exact ⟨hd.2.1,hresult.1,hresult.2.2.1,hresult.2.2.2⟩

end
end SlowEquilibration.PairConditionalDeterminantMoments
