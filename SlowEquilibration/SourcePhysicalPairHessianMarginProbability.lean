-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairHessianMarginIdentity

/-! Actual compact spectral-gap posterior Hessian-margin failure is
exponentially small by the genuine physical GOE matrix law. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open NegativeDefiniteOperators SphericalMarkedWindows IntrinsicHessianLaw ConditionedIntrinsicHessian
open WholeFieldRegression SphericalSequentialRegression PureConditionedHessian ValueTangentConditioning
open SphericalPosteriorMaps
open GOEMaximumDeterminant GOEAsymptotics OAI.CriticalSK
open scoped RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma source_shifted_negative_matrix_measurable (m:ℕ) (κ:ℝ) :
    MeasurableSet {W:Matrix (Fin m) (Fin m) ℝ|
      ¬NegativeDefinite (gaussianMatrixCLM (matrixToGaussian (W+κ • 1)))}:=by
  exact ((isOpen_negativeDefinite (E:=EuclideanSpace ℝ (Fin m))).measurableSet.preimage
    ((matrixOperator_measurable m).comp (by fun_prop))).compl

theorem sourceHessianMargin_failure_of_matrix_law {n P:ℕ} (c:Degree P→ℝ) (κ b k:ℝ)
    (u:Vector (n+2)) (hu:‖u‖^2=(n+2:ℕ)) (ν:Measure (Disorder (n+2) P)) [IsFiniteMeasure ν]
    (hH:HasLaw (intrinsicMatrix c u hu)
      ((goeLaw (n+1) (n+2) b).map (fun W=>W-k • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℝ))) ν) :
    ν.real {J|¬sourceHessianMargin c κ J u} ≤ (goeLaw (n+1) (n+2) b).real (maximumEvent n (k-κ))ᶜ:=by
  have hsub:{J:Disorder (n+2) P|¬sourceHessianMargin c κ J u} ⊆
      {J|¬NegativeDefinite (gaussianMatrixCLM (matrixToGaussian (intrinsicMatrix c u hu J+κ • 1)))}:=by
    intro J hbad hneg
    exact hbad (sourceHessianMargin_of_negative_matrix c κ J u hu hneg)
  apply (measureReal_mono hsub).trans
  rw [hH.measureReal_eq (source_shifted_negative_matrix_measurable (n+1) κ),
    map_measureReal_apply (by fun_prop) (source_shifted_negative_matrix_measurable (n+1) κ)]
  apply le_of_eq
  apply measureReal_congr
  filter_upwards [goe_symmetric_ae (n+1) (n+2) b] with W hW
  have he:W-k • (1:Matrix (Fin (n+1)) (Fin (n+1)) ℝ)+κ • 1=W-(k-κ) • 1:=by module
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_compl_iff,he,
    negativeDefinite_shifted_matrix_iff W hW (k-κ)]

theorem source_mixed_physical_posterior_hessian_margin (μ:FiniteMixture) {Q g:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hg:0<g) :
    ∀ᶠ n:ℕ in atTop,∀ (u:Vector (n+2)) (hu:‖u‖^2=(n+2:ℕ)),∀ h k:ℝ,
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ k →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (mixedConditionedLaw c u hu (WithLp.toLp 2 ![h,k])).real
        {J|¬sourceHessianMargin c (g/2) J u} ≤
        Real.exp (-(n+1:ℝ)*((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2)):=by
  have hb:0<Q^2*μ.xi2 Q:=mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  filter_upwards [nonmaximum_probability_eventually (g:=g/2) hb (div_pos hg (by norm_num))] with n hn
  intro u hu h k hk
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let z:EuclideanSpace ℝ (Fin 2):=WithLp.toLp 2 ![h,k]
  let ν:=mixedConditionedLaw c u hu z
  let :IsProbabilityMeasure ν:=by unfold ν mixedConditionedLaw;infer_instance
  have hshift:jointScoreTarget (n+1) (((n+2:ℕ):ℝ) • z) (Sum.inl 1)/(n+2:ℕ)=k:=by
    change ((n+2:ℕ)*k)/(n+2:ℕ)=k
    field_simp
  have hLaw:=conditioned_intrinsicMatrix_hasLaw μ hQ hnp u hu
    (jointScoreTarget (n+1) (((n+2:ℕ):ℝ) • z))
  simp only [hshift] at hLaw
  have hbnd:=sourceHessianMargin_failure_of_matrix_law c (g/2) (Q^2*μ.xi2 Q) k u hu ν hLaw
  exact hbnd.trans (hn (k-g/2) (by linarith))

theorem source_pure_physical_posterior_hessian_margin (p:ℕ) (hp:2 ≤ p)
    (alpha:ℝ) (halpha:0<alpha) {Q g:ℝ} (hQ:0<Q) (hg:0<g) :
    let μ:=FiniteMixture.pure p hp alpha halpha
    ∀ᶠ n:ℕ in atTop,∀ (u:Vector (n+2)) (hu:‖u‖^2=(n+2:ℕ)),∀ h:ℝ,
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*h →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (valueConditionedLaw c u hu h).real {J|¬sourceHessianMargin c (g/2) J u} ≤
        Real.exp (-(n+1:ℝ)*((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2)):=by
  dsimp only
  let μ:=FiniteMixture.pure p hp alpha halpha
  have hb:0<Q^2*μ.xi2 Q:=mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  filter_upwards [nonmaximum_probability_eventually (g:=g/2) hb (div_pos hg (by norm_num))] with n hn
  intro u hu h hh
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let ν:=valueConditionedLaw c u hu h
  let :IsProbabilityMeasure ν:=by unfold ν valueConditionedLaw;infer_instance
  have hshift:(p:ℝ)*jointValueTarget (n+1) ((n+2:ℕ)*h) (Sum.inl 0)/(n+2:ℕ)=(p:ℝ)*h:=by
    change ((p:ℝ)*((n+2:ℕ)*h))/(n+2:ℕ)=(p:ℝ)*h
    field_simp
  have hLaw:=pure_conditioned_intrinsicMatrix_hasLaw p hp alpha halpha hQ u hu
    (jointValueTarget (n+1) ((n+2:ℕ)*h))
  simp only [hshift] at hLaw
  have hbnd:=sourceHessianMargin_failure_of_matrix_law c (g/2) (Q^2*μ.xi2 Q) ((p:ℝ)*h) u hu ν hLaw
  exact hbnd.trans (hn ((p:ℝ)*h-g/2) (by linarith))

end
end SlowEquilibration.PairConditionalDeterminantMoments
