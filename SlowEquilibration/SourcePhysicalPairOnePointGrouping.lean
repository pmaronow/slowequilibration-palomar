-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPosteriorMeanBounds
public import SlowEquilibration.ObservationTargetEquiv
public import SlowEquilibration.SphericalMarkedWindows

/-! Exact equality of the original physical one-point posteriors and the
normalized whole-coefficient kernels at every physical target. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open NormalizedPairObservations PairObservationTargets NormalizedObservationCoercivity
open GaussianObservationCoercivity ObservationTargetEquiv IntrinsicHessianLaw
open SphericalSequentialRegression SphericalMarkedWindows
open ValueTangentConditioning PureConditionedHessian
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceMixedPhysicalEquiv (N m:ℕ) (hN:0<N) :
    MixedObservationSpace m≃L[ℝ]EuclideanSpace ℝ (Sum (Fin 2) (Fin m)):=
  {toLinearEquiv:=
   {toFun:=fun v=>WithLp.toLp 2 (Sum.elim (fun i=>Real.sqrt N*v.fst i) v.snd)
    invFun:=fun v=>WithLp.toLp 2 (WithLp.toLp 2 (fun i=>(Real.sqrt N)⁻¹*v (Sum.inl i)),
      WithLp.toLp 2 (fun i=>v (Sum.inr i)))
    left_inv:=by
      intro v
      apply WithLp.ofLp_injective
      apply Prod.ext
      · apply WithLp.ofLp_injective
        funext i
        change (Real.sqrt N)⁻¹*(Real.sqrt N*v.fst i)=v.fst i
        rw [←mul_assoc,inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)),one_mul]
      · rfl
    right_inv:=by
      intro v
      apply WithLp.ofLp_injective
      funext i
      cases i with
      | inl i=>
        change Real.sqrt N*((Real.sqrt N)⁻¹*v (Sum.inl i))=v (Sum.inl i)
        rw [←mul_assoc,mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)),one_mul]
      | inr i=>rfl
    map_add':=by intros;apply WithLp.ofLp_injective;funext i;cases i <;> simp [mul_add]
    map_smul':=by intros;apply WithLp.ofLp_injective;funext i;cases i <;> simp [mul_left_comm]}
   continuous_toFun:=by
     apply (PiLp.continuous_toLp 2 _).comp
     apply continuous_pi
     intro i
     cases i with
     | inl i=>exact continuous_const.mul ((PiLp.continuous_apply 2 _ i).comp (WithLp.continuous_fst 2 _ _))
     | inr i=>exact (PiLp.continuous_apply 2 _ i).comp (WithLp.continuous_snd 2 _ _)
   continuous_invFun:=by
     apply (WithLp.prod_continuous_toLp 2 (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin m))).comp
     apply Continuous.prodMk
     · apply (PiLp.continuous_toLp 2 _).comp
       exact continuous_pi (fun i=>continuous_const.mul (PiLp.continuous_apply 2 _ (Sum.inl i)))
     · apply (PiLp.continuous_toLp 2 _).comp
       exact continuous_pi (fun i=>PiLp.continuous_apply 2 _ (Sum.inr i))}

lemma sourceMixedPhysicalEquiv_observation {N P m:ℕ} (hN:0<N) (c:Degree P→ℝ)
    (x:Vector N) (e:Fin m→Vector N) :
    (sourceMixedPhysicalEquiv N m hN).toContinuousLinearMap.comp (singleMixedObservation c x e)=
      jointCLM c x e:=by
  ext g i
  cases i with
  | inl i=>
    change Real.sqrt N*((Real.sqrt N)⁻¹*scoreCLM c x g i)=scoreCLM c x g i
    rw [←mul_assoc,mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)),one_mul]
  | inr i=>rfl

lemma sourceMixedPhysicalEquiv_target (n:ℕ) (h k:ℝ) :
    sourceMixedPhysicalEquiv (n+1) n (by omega) (mixedPointTarget (n+1) n h k)=
      jointScoreTarget n (((n+1:ℕ):ℝ) • (WithLp.toLp 2 ![h,k]:EuclideanSpace ℝ (Fin 2))):=by
  ext i
  cases i with
  | inl i=>
    fin_cases i <;> change Real.sqrt (n+1:ℕ)*(Real.sqrt (n+1:ℕ)*_)=(n+1:ℕ)*_
    all_goals rw [←mul_assoc,Real.mul_self_sqrt (by positivity)];rfl
  | inr i=>rfl

theorem source_mixed_physical_one_point_posterior_grouping (n:ℕ) (μ:FiniteMixture) {Q:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (x:Vector (n+1))
    (hx:‖x‖^2=(n+1:ℕ)) (h k:ℝ) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    mixedConditionedLaw c x hx (WithLp.toLp 2 ![h,k])=
      coefficientKernel (singleMixedObservation c x (tangentFrame x hx))
        (mixedPointTarget (n+1) n h k):=by
  dsimp only
  obtain ⟨δ,hδ,hcoerc⟩:=uniform_mixed_coercivity μ hQ hnp
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let A:=singleMixedObservation c x (tangentFrame x hx)
  have hA:Surjective A:=observation_surjective _ hδ
    (hcoerc (n+1) n (by omega) x hx _ (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx))
  have hh:=coefficientKernel_target_equiv A hA (sourceMixedPhysicalEquiv (n+1) n (by omega))
    (mixedPointTarget (n+1) n h k)
  simpa only [A,c,sourceMixedPhysicalEquiv_observation,sourceMixedPhysicalEquiv_target,mixedConditionedLaw] using hh

end
end SlowEquilibration.PairConditionalDeterminantMoments
