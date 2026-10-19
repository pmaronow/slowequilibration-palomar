-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorResidualLaw
public import SlowEquilibration.SphericalPureMarkedWindows

@[expose] public section
/-! Actual transverse Taylor remainders retain their whole continuous
sample-function law under either genuine critical-point posterior. The
coefficient annihilation is proved from the original tensor covariance;
no TAP formula, band pressure, or thermodynamic limit is assumed. -/
namespace SlowEquilibration.SphericalTAPCriticalBand
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicHessianLaw
open ConditionedIntrinsicHessian ValueTangentConditioning SphericalMarkedWindows
open SphericalTaylorRemainder GaussianRegression
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual posterior invariance for a Banach-valued linear observable;
the target need not be a finite-dimensional Euclidean observation. -/
theorem actual_coefficientKernel_continuous_linear_annihilator
    {N P:ℕ} {F G:Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
    (A:EuclideanDisorder N P→L[ℝ] F) (B:EuclideanDisorder N P→L[ℝ] G)
    (hBA:B.comp A.adjoint=0) (w:F) :
    (coefficientKernel A w).map (actualObservation B)=
      (disorderLaw N P).map (actualObservation B):=by
  have hm:Measurable (actualObservation B):=B.continuous.measurable.comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _:Coordinate N P=>ℝ)).symm.continuous.measurable.comp
      (flatDisorder_measurable N P))
  have hBlift (v:F):B (lift A v)=0:=by
    exact congrArg (fun L:F→L[ℝ] G=>L ((gram A).inverse v)) hBA
  have hBres (g:EuclideanDisorder N P):B (residual A g)=B g:=by
    change B (g-lift A (A g))=B g
    rw [map_sub,hBlift,sub_zero]
  rw [coefficientKernel_apply,regressionKernel_apply,
    Measure.map_map hm (unpackCLM N P).continuous.measurable,
    Measure.map_map (hm.comp (unpackCLM N P).continuous.measurable) (by fun_prop)]
  have he:(actualObservation B∘unpackCLM N P)∘(fun g=>residual A g+lift A w)=B:=by
    funext g
    change B (residual A g+lift A w)=B g
    rw [map_add,hBres,hBlift,add_zero]
  rw [he]
  exact ((hasLaw_map B.continuous.measurable.aemeasurable).fun_comp
    (actual_flattened_gaussian N P)).map_eq.symm

theorem actual_taylorRemainder_joint_adjoint_zero {N P k:ℕ} (hN:0<N)
    (c:Degree P→ℝ) (hc:∀ p,0 ≤ c p) (u:Vector N) (e:Fin k→Vector N)
    (z:Vector N) (hz:inner ℝ z u=0) :
    (taylorRemainderCLM c u z).comp (jointCLM c u e).adjoint=0:=by
  apply scalar_comp_adjoint_eq_zero
  intro i
  cases i with
  | inl i =>
    fin_cases i
    · have heq:(EuclideanSpace.proj (Sum.inl (0:Fin 2))).comp (jointCLM c u e)=
          valueObservation c u:=by
        ext g
        change jointCLM c u e g (Sum.inl 0)=valueObservation c u g
        simp only [jointCLM_apply_inl,
          scoreCLM_apply_zero,valueObservation,flatJetCLM_apply]
      change (taylorRemainderCLM c u z)
        (((EuclideanSpace.proj (Sum.inl (0:Fin 2))).comp (jointCLM c u e)).adjoint 1)=0
      rw [heq]
      exact taylorRemainder_value_orthogonal hN c hc u z hz
    · have heq:(EuclideanSpace.proj (Sum.inl (1:Fin 2))).comp (jointCLM c u e)=
          directionObservation c u u:=by
        ext g
        change jointCLM c u e g (Sum.inl 1)=directionObservation c u u g
        simp only [jointCLM_apply_inl,
          scoreCLM_apply_one,directionObservation,flatJetCLM_apply]
      change (taylorRemainderCLM c u z)
        (((EuclideanSpace.proj (Sum.inl (1:Fin 2))).comp (jointCLM c u e)).adjoint 1)=0
      rw [heq]
      exact taylorRemainder_direction_orthogonal hN c hc u z u hz
  | inr i =>
    have heq:(EuclideanSpace.proj (Sum.inr i)).comp (jointCLM c u e)=
        directionObservation c u (e i):=by
      ext g
      change jointCLM c u e g (Sum.inr i)=directionObservation c u (e i) g
      simp only [jointCLM_apply_inr,
        gradientCLM_apply,directionObservation,flatJetCLM_apply]
    rw [heq]
    exact taylorRemainder_direction_orthogonal hN c hc u z (e i) hz

theorem actual_taylorRemainder_value_adjoint_zero {N P k:ℕ} (hN:0<N)
    (c:Degree P→ℝ) (hc:∀ p,0 ≤ c p) (u:Vector N) (e:Fin k→Vector N)
    (z:Vector N) (hz:inner ℝ z u=0) :
    (taylorRemainderCLM c u z).comp (valueTangentCLM c u e).adjoint=0:=by
  rw [valueTangentCLM,ContinuousLinearMap.adjoint_comp,←ContinuousLinearMap.comp_assoc,
    actual_taylorRemainder_joint_adjoint_zero hN c hc u e z hz,ContinuousLinearMap.zero_comp]

variable {K:Type*} [TopologicalSpace K] [CompactSpace K]

/-- Equality of the entire true C(K)-valued field law at every mixed
value/radial/tangent observation target, including prescribed null marks. -/
theorem actual_critical_taylorContinuousField_joint_law {N P k:ℕ} (hN:0<N)
    (c:Degree P→ℝ) (hc:∀ p,0 ≤ c p) (u:Vector N) (e:Fin k→Vector N)
    (z:K→Vector N) (hz:Continuous z) (ht:∀ x,inner ℝ (z x) u=0)
    (w:EuclideanSpace ℝ (Sum (Fin 2) (Fin k))) :
    (coefficientKernel (jointCLM c u e) w).map
      (fun J=>taylorContinuousField c u z hz (euclideanDisorder J))=
    (disorderLaw N P).map (fun J=>taylorContinuousField c u z hz (euclideanDisorder J)):=by
  apply actual_coefficientKernel_continuous_linear_annihilator
  ext a x
  change taylorRemainderCLM c u (z x) ((jointCLM c u e).adjoint a)=0
  exact congrArg (fun L=>L a) (actual_taylorRemainder_joint_adjoint_zero hN c hc u e (z x) (ht x))

/-- The same genuine whole sample-function law for proper value-only
conditioning, with no redundant radial inverse. -/
theorem actual_critical_taylorContinuousField_value_law {N P k:ℕ} (hN:0<N)
    (c:Degree P→ℝ) (hc:∀ p,0 ≤ c p) (u:Vector N) (e:Fin k→Vector N)
    (z:K→Vector N) (hz:Continuous z) (ht:∀ x,inner ℝ (z x) u=0)
    (w:EuclideanSpace ℝ (Sum (Fin 1) (Fin k))) :
    (coefficientKernel (valueTangentCLM c u e) w).map
      (fun J=>taylorContinuousField c u z hz (euclideanDisorder J))=
    (disorderLaw N P).map (fun J=>taylorContinuousField c u z hz (euclideanDisorder J)):=by
  apply actual_coefficientKernel_continuous_linear_annihilator
  ext a x
  change taylorRemainderCLM c u (z x) ((valueTangentCLM c u e).adjoint a)=0
  exact congrArg (fun L=>L a) (actual_taylorRemainder_value_adjoint_zero hN c hc u e (z x) (ht x))

end
end SlowEquilibration.SphericalTAPCriticalBand
