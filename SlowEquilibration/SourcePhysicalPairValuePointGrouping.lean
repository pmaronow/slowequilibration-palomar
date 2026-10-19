-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairOnePointGrouping
public import SlowEquilibration.SphericalPureMarkedWindows

/-! The proper physical value-only posterior is the actual normalized
coefficient kernel, including the pure model with redundant radial score
omitted. The identity holds at every physical value target. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression GaussianRegression
open NormalizedPairObservations PairObservationTargets NormalizedObservationCoercivity
open GaussianObservationCoercivity ObservationTargetEquiv IntrinsicHessianLaw
open SphericalMarkedWindows ValueTangentConditioning PureConditionedHessian
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceValuePhysicalEquiv (N m:ℕ) (hN:0<N) :
    ValueObservationSpace m≃L[ℝ]EuclideanSpace ℝ (Sum (Fin 1) (Fin m)):=
  {toLinearEquiv:=
   {toFun:=fun v=>WithLp.toLp 2 (Sum.elim (fun _=>Real.sqrt N*v.fst) v.snd)
    invFun:=fun v=>WithLp.toLp 2 ((Real.sqrt N)⁻¹*v (Sum.inl 0),
      WithLp.toLp 2 (fun i=>v (Sum.inr i)))
    left_inv:=by
      intro v
      apply WithLp.ofLp_injective
      apply Prod.ext
      · change (Real.sqrt N)⁻¹*(Real.sqrt N*v.fst)=v.fst
        rw [←mul_assoc,inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)),one_mul]
      · rfl
    right_inv:=by
      intro v
      apply WithLp.ofLp_injective
      funext i
      cases i with
      | inl i=>
        fin_cases i
        change Real.sqrt N*((Real.sqrt N)⁻¹*v (Sum.inl 0))=v (Sum.inl 0)
        rw [←mul_assoc,mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)),one_mul]
      | inr i=>rfl
    map_add':=by intros;apply WithLp.ofLp_injective;funext i;cases i <;> simp [mul_add]
    map_smul':=by intros;apply WithLp.ofLp_injective;funext i;cases i <;> simp [mul_left_comm]}
   continuous_toFun:=by
     apply (PiLp.continuous_toLp 2 _).comp
     apply continuous_pi
     intro i
     cases i with
     | inl _=>exact continuous_const.mul (WithLp.continuous_fst 2 _ _)
     | inr i=>exact (PiLp.continuous_apply 2 _ i).comp (WithLp.continuous_snd 2 _ _)
   continuous_invFun:=by
     apply (WithLp.prod_continuous_toLp 2 ℝ (EuclideanSpace ℝ (Fin m))).comp
     apply Continuous.prodMk
     · exact continuous_const.mul (PiLp.continuous_apply 2 _ (Sum.inl 0))
     · apply (PiLp.continuous_toLp 2 _).comp
       exact continuous_pi (fun i=>PiLp.continuous_apply 2 _ (Sum.inr i))}

lemma sourceValuePhysicalEquiv_observation {N P m:ℕ} (hN:0<N) (c:Degree P→ℝ)
    (x:Vector N) (e:Fin m→Vector N) :
    (sourceValuePhysicalEquiv N m hN).toContinuousLinearMap.comp (singleValueObservation c x e)=
      valueTangentCLM c x e:=by
  ext g i
  cases i with
  | inl i=>
    change Real.sqrt N*((Real.sqrt N)⁻¹*flatJetCLM c 0 x (fun i=>Fin.elim0 i) g)=_
    rw [←mul_assoc,mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)),one_mul]
    rfl
  | inr i=>rfl

lemma sourceValuePhysicalEquiv_target (n:ℕ) (h:ℝ) :
    sourceValuePhysicalEquiv (n+1) n (by omega) (valuePointTarget (n+1) n h)=valueTarget n h:=by
  ext i
  cases i with
  | inl i=>
    change Real.sqrt (n+1:ℕ)*(Real.sqrt (n+1:ℕ)*h)=(n+1:ℕ)*h
    rw [←mul_assoc,Real.mul_self_sqrt (by positivity)]
  | inr i=>rfl

theorem source_value_physical_one_point_posterior_grouping (n:ℕ) (μ:FiniteMixture) {Q:ℝ}
    (hQ:0<Q) (x:Vector (n+1)) (hx:‖x‖^2=(n+1:ℕ)) (h:ℝ) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    valueConditionedLaw c x hx h=
      coefficientKernel (singleValueObservation c x (tangentFrame x hx))
        (valuePointTarget (n+1) n h):=by
  dsimp only
  obtain ⟨δ,hδ,hcoerc⟩:=uniform_value_coercivity μ hQ
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let A:=singleValueObservation c x (tangentFrame x hx)
  have hA:Surjective A:=observation_surjective _ hδ
    (hcoerc (n+1) n (by omega) x hx _ (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx))
  have hh:=coefficientKernel_target_equiv A hA (sourceValuePhysicalEquiv (n+1) n (by omega))
    (valuePointTarget (n+1) n h)
  have ht:valueTarget n h=SphericalSequentialRegression.jointValueTarget n ((n+1:ℕ)*h):=by
    ext i
    cases i <;> rfl
  simpa only [A,c,sourceValuePhysicalEquiv_observation,sourceValuePhysicalEquiv_target,ht,valueConditionedLaw] using hh

end
end SlowEquilibration.PairConditionalDeterminantMoments
