-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairDetWeightMeasurable
public import SlowEquilibration.PhysicalMarkWindowDisintegration

/-! Exact physical score/value window disintegration of the original
intrinsic pair Kac--Rice integrand, retaining arbitrary Borel full-field marks. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations SphericalForm
open GaussianRegression GaussianObservationCoercivity IntrinsicHessianLaw
open IntrinsicGradientRegression SphericalPairIntrinsicCoordinates SphericalPairMarkedWindows SphericalMarkedWindows
open scoped ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 500000
attribute [local instance] Classical.propDecidable

theorem source_mixed_physical_pair_window_disintegration (μ:FiniteMixture) {Q:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) :
    ∃ η:ℝ,0<η ∧ ∀ n:ℕ,∀ (x y:Vector (n+3))
      (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)), |overlap x y| ≤ η →
      ∀ (K:Set (EuclideanSpace ℝ (Fin 2))),MeasurableSet K →
      ∀ (phi:Disorder (n+3) μ.maxDegree→ℝ≥0∞),Measurable phi →
  let c:Degree μ.maxDegree→ℝ:=centerCoefficients (mixtureCoefficients μ) Q
      let D:=intrinsicPairDetWeight c x y
      intrinsicMixedPairWindowIntensity c x y K phi=
        observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0*
          ∫⁻ b in {b:ScorePairSpace|b.fst∈K ∧ b.snd∈K},pairMixedPhysicalPdf c x y hx hy b*
            ∫⁻ J,D J*phi J ∂pairMixedConditionedLaw c x y hx hy b:=by
  obtain ⟨η1,hη1,hDis⟩:=uniform_intrinsic_physical_mixed_disintegration μ hQ hnp hd
  obtain ⟨η2,hη2,hFiber⟩:=source_mixed_physical_pair_marks_ae μ hQ hnp hd
  refine ⟨min η1 η2,lt_min hη1 hη2,?_⟩
  intro n x y hx hy hr K hK phi hphi
  dsimp only
  unfold intrinsicMixedPairWindowIntensity
  let c:Degree μ.maxDegree→ℝ:=centerCoefficients (mixtureCoefficients μ) Q
  let D:=intrinsicPairDetWeight c x y
  let B:={b:ScorePairSpace|b.fst∈K ∧ b.snd∈K}
  let q:=fun J:Disorder (n+3) μ.maxDegree=>
    (WithLp.toLp 2 (actualScore c J x,actualScore c J y):ScorePairSpace)
  have hxs:Measurable (fun J:Disorder (n+3) μ.maxDegree=>actualScore c J x):=by
    simpa only [Function.comp_def,id_eq] using (actualScore_jointContinuous (N:=n+3) (P:=μ.maxDegree) c).measurable.comp (measurable_id.prodMk measurable_const)
  have hys:Measurable (fun J:Disorder (n+3) μ.maxDegree=>actualScore c J y):=by
    simpa only [Function.comp_def,id_eq] using (actualScore_jointContinuous (N:=n+3) (P:=μ.maxDegree) c).measurable.comp (measurable_id.prodMk measurable_const)
  have hB:MeasurableSet B:=(hK.preimage (WithLp.continuous_fst 2 (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))).measurable).inter
    (hK.preimage (WithLp.continuous_snd 2 (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))).measurable)
  have hq:Measurable q:=by
    change Measurable ((WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))).symm ∘ (fun J=>(actualScore c J x,actualScore c J y)))
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))).symm.continuous.measurable.comp (hxs.prodMk hys)
  have hF:∀ b,∀ᵐ J ∂pairMixedConditionedLaw c x y hx hy b,q J=b:=by
    intro b
    filter_upwards [hFiber n x y hx hy (hr.trans (min_le_right _ _)) b] with J hJ
    apply WithLp.ofLp_injective
    exact Prod.ext hJ.1 hJ.2
  have hPhys:∀ (f:Disorder (n+3) μ.maxDegree→ℝ≥0∞),Measurable f →
      observationPdf (pairIntrinsicGamma c x y) 0*(∫⁻ J,f J ∂coefficientKernel (pairIntrinsicGamma c x y) 0)=
        observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0*
          ∫⁻ b,pairMixedPhysicalPdf c x y hx hy b*∫⁻ J,f J ∂pairMixedConditionedLaw c x y hx hy b:=
    (hDis (n+2) x y hx hy (hr.trans (min_le_left _ _))).2
  have hWin (J:Disorder (n+3) μ.maxDegree):
      (@ite ℝ≥0∞ (q J∈B) (Classical.propDecidable _) (phi J) 0)=(if actualScore c J x∈K ∧ actualScore c J y∈K then phi J else 0):=by
    have hmem:q J∈B ↔ actualScore c J x∈K ∧ actualScore c J y∈K:=by rfl
    by_cases h:actualScore c J x∈K ∧ actualScore c J y∈K
    · rw [ite_eq_left h,ite_eq_left (hmem.mpr h)]
    · rw [ite_eq_right h,ite_eq_right (fun hh=>h (hmem.mp hh))]
  have ht:=physical_mark_window_disintegration volume _ _ q hq D phi
    (intrinsicPairDetWeight_measurable c x y hx hy) hphi B hB _ _ _ hF hPhys
  calc
    _ = observationPdf (pairIntrinsicGamma c x y) 0*
        (∫⁻ J,D J*(@ite ℝ≥0∞ (q J∈B) (Classical.propDecidable _) (phi J) 0) ∂coefficientKernel (pairIntrinsicGamma c x y) 0):=by
      apply congrArg (fun t:ℝ≥0∞=>observationPdf (pairIntrinsicGamma c x y) 0*t)
      apply lintegral_congr
      intro J
      exact congrArg (fun t:ℝ≥0∞=>D J*t) (hWin J).symm
    _ = _:=ht

theorem source_value_physical_pair_window_disintegration (μ:FiniteMixture) {Q:ℝ}
    (hQ:0<Q) (hd:4 ≤ μ.minDegree) :
    ∃ η:ℝ,0<η ∧ ∀ n:ℕ,∀ (x y:Vector (n+3))
      (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)), |overlap x y| ≤ η →
      ∀ (K:Set (ℝ)),MeasurableSet K →
      ∀ (phi:Disorder (n+3) μ.maxDegree→ℝ≥0∞),Measurable phi →
  let c:Degree μ.maxDegree→ℝ:=centerCoefficients (mixtureCoefficients μ) Q
      let D:=intrinsicPairDetWeight c x y
      intrinsicValuePairWindowIntensity c x y K phi=
        observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0*
          ∫⁻ b in {b:ValuePairSpace|b.fst∈K ∧ b.snd∈K},pairValuePhysicalPdf c x y hx hy b*
            ∫⁻ J,D J*phi J ∂pairValueConditionedLaw c x y hx hy b:=by
  obtain ⟨η1,hη1,hDis⟩:=uniform_intrinsic_physical_value_disintegration μ hQ hd
  obtain ⟨η2,hη2,hFiber⟩:=source_value_physical_pair_marks_ae μ hQ hd
  refine ⟨min η1 η2,lt_min hη1 hη2,?_⟩
  intro n x y hx hy hr K hK phi hphi
  dsimp only
  unfold intrinsicValuePairWindowIntensity
  let c:Degree μ.maxDegree→ℝ:=centerCoefficients (mixtureCoefficients μ) Q
  let D:=intrinsicPairDetWeight c x y
  let B:={b:ValuePairSpace|b.fst∈K ∧ b.snd∈K}
  let q:=fun J:Disorder (n+3) μ.maxDegree=>
    (WithLp.toLp 2 (actualValue c J x,actualValue c J y):ValuePairSpace)
  have hxs:Measurable (fun J:Disorder (n+3) μ.maxDegree=>actualValue c J x):=by
    simpa only [Function.comp_def,id_eq] using (actualValue_jointContinuous (N:=n+3) (P:=μ.maxDegree) c).measurable.comp (measurable_id.prodMk measurable_const)
  have hys:Measurable (fun J:Disorder (n+3) μ.maxDegree=>actualValue c J y):=by
    simpa only [Function.comp_def,id_eq] using (actualValue_jointContinuous (N:=n+3) (P:=μ.maxDegree) c).measurable.comp (measurable_id.prodMk measurable_const)
  have hB:MeasurableSet B:=(hK.preimage (WithLp.continuous_fst 2 (ℝ) (ℝ)).measurable).inter
    (hK.preimage (WithLp.continuous_snd 2 (ℝ) (ℝ)).measurable)
  have hq:Measurable q:=by
    change Measurable ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm ∘ (fun J=>(actualValue c J x,actualValue c J y)))
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.continuous.measurable.comp (hxs.prodMk hys)
  have hF:∀ b,∀ᵐ J ∂pairValueConditionedLaw c x y hx hy b,q J=b:=by
    intro b
    filter_upwards [hFiber n x y hx hy (hr.trans (min_le_right _ _)) b] with J hJ
    apply WithLp.ofLp_injective
    exact Prod.ext hJ.1 hJ.2
  have hPhys:∀ (f:Disorder (n+3) μ.maxDegree→ℝ≥0∞),Measurable f →
      observationPdf (pairIntrinsicGamma c x y) 0*(∫⁻ J,f J ∂coefficientKernel (pairIntrinsicGamma c x y) 0)=
        observationPdf (pairGradient c x y (tangentFrame x hx) (tangentFrame y hy)) 0*
          ∫⁻ b,pairValuePhysicalPdf c x y hx hy b*∫⁻ J,f J ∂pairValueConditionedLaw c x y hx hy b:=
    (hDis (n+2) x y hx hy (hr.trans (min_le_left _ _))).2
  have hWin (J:Disorder (n+3) μ.maxDegree):
      (@ite ℝ≥0∞ (q J∈B) (Classical.propDecidable _) (phi J) 0)=(if actualValue c J x∈K ∧ actualValue c J y∈K then phi J else 0):=by
    have hmem:q J∈B ↔ actualValue c J x∈K ∧ actualValue c J y∈K:=by rfl
    by_cases h:actualValue c J x∈K ∧ actualValue c J y∈K
    · rw [ite_eq_left h,ite_eq_left (hmem.mpr h)]
    · rw [ite_eq_right h,ite_eq_right (fun hh=>h (hmem.mp hh))]
  have ht:=physical_mark_window_disintegration volume _ _ q hq D phi
    (intrinsicPairDetWeight_measurable c x y hx hy) hphi B hB _ _ _ hF hPhys
  calc
    _ = observationPdf (pairIntrinsicGamma c x y) 0*
        (∫⁻ J,D J*(@ite ℝ≥0∞ (q J∈B) (Classical.propDecidable _) (phi J) 0) ∂coefficientKernel (pairIntrinsicGamma c x y) 0):=by
      apply congrArg (fun t:ℝ≥0∞=>observationPdf (pairIntrinsicGamma c x y) 0*t)
      apply lintegral_congr
      intro J
      exact congrArg (fun t:ℝ≥0∞=>D J*t) (hWin J).symm
    _ = _:=ht

end
end SlowEquilibration.PairConditionalDeterminantMoments
