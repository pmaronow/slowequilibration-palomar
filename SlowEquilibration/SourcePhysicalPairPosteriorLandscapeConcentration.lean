-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairProjectedLandscapeBounds
public import SlowEquilibration.SourcePhysicalPairPosteriorJetConcentration

/-! Full ordered-tensor regularity under the genuine coefficient posterior,
with a compact-mark mean shift derived from the actual observation lift. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open SphericalAging.GaussianLandscape
open NormalizedPairObservations PairObservationTargets NormalizedObservationCoercivity
open GaussianObservationCoercivity
open scoped ENNReal BigOperators
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem source_posterior_tensorNorm_tail {N P:ℕ} {F:Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (hN:0<N) (A:EuclideanDisorder N P→L[ℝ]F) (hA:Surjective A)
    (w:F) {K:ℝ} (hm:‖lift A w‖ ≤ K*Real.sqrt N) (p:Degree P) :
    (coefficientKernel A w).real
      {J|(2*((p.val.val:ℝ)+1)+1+K)*Real.sqrt N ≤ ‖tensorForm N p.val.val (J p)‖} ≤
      Real.exp (-(N:ℝ)/2):=by
  let T:EuclideanDisorder N P→L[ℝ]EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N p.val.val):=
    (sourceDegreeProjectionCLM p).comp (residual A)
  have hr:‖residual A‖ ≤ 1:=by rw [residual_eq_starProjection A hA];exact A.ker.starProjection_norm_le
  have hT:‖T‖ ≤ 1:=by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [sourceDegreeProjectionCLM_norm_le (N:=N) p,norm_nonneg (sourceDegreeProjectionCLM (N:=N) p)])
  let m:=sourceDegreeProjectionCLM p (lift A w)
  have hshift:‖m‖ ≤ K*Real.sqrt N:=by
    exact ((sourceDegreeProjectionCLM p).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (sourceDegreeProjectionCLM_norm_le p) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hm))
  have ht:=sourceProjectedAffineTensorNorm_tail hN T hT m hshift
  have hB:MeasurableSet {J:SphericalModel.Disorder N P|
      (2*((p.val.val:ℝ)+1)+1+K)*Real.sqrt N ≤ ‖tensorForm N p.val.val (J p)‖}:=
    measurableSet_le measurable_const
      ((tensorForm_continuous N p.val.val).norm.measurable.comp (measurable_pi_apply p))
  rw [sourceCoefficientKernel_affine A w,map_measureReal_apply (by fun_prop) hB]
  convert ht using 1
  congr 1

def sourcePosteriorOrderedRegularity {N P:ℕ} (K:ℝ) : Set (SphericalModel.Disorder N P):=
  {J|∀ p:Degree P,landscapeNorm N p.val.val (J p) ≤ 2*((p.val.val:ℝ)+1)+1+K}

lemma sourcePosteriorOrderedRegularity_measurable (N P:ℕ) (K:ℝ) :
    MeasurableSet (sourcePosteriorOrderedRegularity (N:=N) (P:=P) K):=by
  have he:sourcePosteriorOrderedRegularity (N:=N) (P:=P) K=
      ⋂ p:Degree P,{J:SphericalModel.Disorder N P|landscapeNorm N p.val.val (J p) ≤ 2*((p.val.val:ℝ)+1)+1+K}:=by
    ext J
    simp only [sourcePosteriorOrderedRegularity,Set.mem_ofPred_eq,Set.mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun p=>measurableSet_le
    ((landscapeNorm_continuous N p.val.val).measurable.comp (measurable_pi_apply p)) measurable_const)

theorem source_posterior_orderedRegularity_failure {N P:ℕ} {F:Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (hN:0<N) (A:EuclideanDisorder N P→L[ℝ]F) (hA:Surjective A)
    (w:F) {K:ℝ} (hm:‖lift A w‖ ≤ K*Real.sqrt N) :
    (coefficientKernel A w).real (sourcePosteriorOrderedRegularity (N:=N) (P:=P) K)ᶜ ≤
      (Fintype.card (Degree P):ℝ)*Real.exp (-(N:ℝ)/2):=by
  classical
  have hsub:(sourcePosteriorOrderedRegularity (N:=N) (P:=P) K)ᶜ ⊆
      ⋃ p:Degree P,{J:SphericalModel.Disorder N P|
        (2*((p.val.val:ℝ)+1)+1+K)*Real.sqrt N ≤ ‖tensorForm N p.val.val (J p)‖}:=by
    intro J hJ
    change ¬∀ p:Degree P,_ at hJ
    obtain ⟨p,hp⟩:=not_forall.mp hJ
    apply Set.mem_iUnion.mpr
    refine ⟨p,?_⟩
    change ¬landscapeNorm N p.val.val (J p) ≤ _ at hp
    exact ((le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))).mp (le_of_lt (lt_of_not_ge hp)))
  refine (measureReal_mono hsub).trans ?_
  calc
    _ ≤ ∑ p:Degree P,(coefficientKernel A w).real
      {J|(2*((p.val.val:ℝ)+1)+1+K)*Real.sqrt N ≤ ‖tensorForm N p.val.val (J p)‖}:=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _p:Degree P,Real.exp (-(N:ℝ)/2):=
      Finset.sum_le_sum (fun p _=>source_posterior_tensorNorm_tail hN A hA w hm p)
    _ = _:=by simp

theorem source_mixed_posterior_orderedRegularity (μ:FiniteMixture) {Q M:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hM:0 ≤ M) :
    ∃ K:ℝ,0<K ∧ ∀ (N m:ℕ),0<N → ∀ (x:Vector N),‖x‖^2=(N:ℝ) →
      ∀ (e:Fin m→Vector N),Orthonormal ℝ e → (∀ i,inner ℝ (e i) x=0) →
      ∀ (h k:ℝ),|h| ≤ M → |k| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (coefficientKernel (singleMixedObservation c x e) (mixedPointTarget N m h k)).real
        (sourcePosteriorOrderedRegularity (N:=N) (P:=μ.maxDegree) K)ᶜ ≤
        (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(N:ℝ)/2):=by
  obtain ⟨K,hK,hmean⟩:=source_mixed_one_point_coefficient_mean_bound μ hQ hnp hM
  obtain ⟨δ,hδ,hcoerc⟩:=uniform_mixed_coercivity μ hQ hnp
  refine ⟨K,hK,?_⟩
  intro N m hN x hx e he htan h k hh hk
  dsimp only
  exact source_posterior_orderedRegularity_failure hN _
    (observation_surjective _ hδ (hcoerc N m hN x hx e he htan)) _
    (hmean N m hN x hx e he htan h k hh hk)

theorem source_value_posterior_orderedRegularity (μ:FiniteMixture) {Q M:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) :
    ∃ K:ℝ,0<K ∧ ∀ (N m:ℕ),0<N → ∀ (x:Vector N),‖x‖^2=(N:ℝ) →
      ∀ (e:Fin m→Vector N),Orthonormal ℝ e → (∀ i,inner ℝ (e i) x=0) →
      ∀ h:ℝ,|h| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (coefficientKernel (singleValueObservation c x e) (valuePointTarget N m h)).real
        (sourcePosteriorOrderedRegularity (N:=N) (P:=μ.maxDegree) K)ᶜ ≤
        (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(N:ℝ)/2):=by
  obtain ⟨K,hK,hmean⟩:=source_value_one_point_coefficient_mean_bound μ hQ hM
  obtain ⟨δ,hδ,hcoerc⟩:=uniform_value_coercivity μ hQ
  refine ⟨K,hK,?_⟩
  intro N m hN x hx e he htan h hh
  dsimp only
  exact source_posterior_orderedRegularity_failure hN _
    (observation_surjective _ hδ (hcoerc N m hN x hx e he htan)) _
    (hmean N m hN x hx e he htan h hh)

end
end SlowEquilibration.PairConditionalDeterminantMoments
