-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCaptureBandComplementBound
public import SlowEquilibration.SourcePureCaptureNormalizedEstimates
public import SlowEquilibration.SourcePureCaptureMaximumUpper

/-! Integrating the actual Gibbs cap-to-band comparison. Finite marked
expectations supply all count integrability; the count, its Hessian, and its
partition mark remain on the same original disorder realization. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourcePureCaptureExpectationBound
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open SphericalGaussianJet SphericalMarkedWindows SphericalMorse
open SourcePureCaptureBandComplementBound SourcePureCapBorelMarkedValue
open SourcePureCaptureFixedCapEstimates PureCapturePhysicalDiagonalBridge
open scoped ENNReal Topology
set_option autoImplicit false

theorem capture_original_marked_count_aemeasurable
    (d : ℕ) (μ : FiniteMixture) (β : ℝ) {E I : Set ℝ}
    (hE : MeasurableSet E) (hI : MeasurableSet I) :
    AEMeasurable (originalEnergyMarkedCount d μ β E I)
      (disorderLaw (d+2) μ.maxDegree) := by
  have hK : MeasurableSet (physicalEnergyWindow (d+2) E univ) :=
    rectangularScoreWindow_measurable _ _
      (hE.preimage (measurable_const_mul ((d+2:ℕ):ℝ))) MeasurableSet.univ
  have hh := actualScoreWindowCount_aemeasurable (d+1) (by omega) μ
    (Q := 1) (by norm_num) _ hK (originalBorelBandMark d μ β I)
      (originalBorelBandMark_measurable d μ β hI)
  have heq := funext (originalEnergyMarkedCount_eq_actualScoreWindowCount d μ β E I)
  rw [heq]
  exact hh

/-- The expected microscopic uncovered mass is bounded by the genuine
coarse-cover error, maximum and denominator failures, and the two actual
marked expectations. Only finite marked expectations and band measurability
are required here, and those are discharged in the pure application. -/
theorem original_expected_band_complement_le
    (d : ℕ) (hd : 1 ≤ d) (μ : FiniteMixture)
    (β a ep τ m L q b η A : ℝ) (hη : 0 < η) (hA : 0 < A)
    (hBandInt : Integrable (fun J : Disorder (d+2) μ.maxDegree =>
      (gibbsLaw (d+2) β (field (mixtureCoefficients μ) J)).real
        (originalEnergyBandUnion d μ m L q b J)ᶜ) (disorderLaw (d+2) μ.maxDegree))
    (hDeep : (∫⁻ J, originalEnergyMarkedCount d μ β
      (Icc ((d+2:ℕ)*(ep-τ)) (m-L)) (Ico a 1) J
      ∂disorderLaw (d+2) μ.maxDegree) ≠ ⊤)
    (hAngular : (∫⁻ J, originalEnergyMarkedCount d μ β
      (Icc (m-L) (m+L)) (Ico a 1 \ Icc (q-b) (q+b)) J
      ∂disorderLaw (d+2) μ.maxDegree) ≠ ⊤) :
    (∫ J, (gibbsLaw (d+2) β (field (mixtureCoefficients μ) J)).real
      (originalEnergyBandUnion d μ m L q b J)ᶜ ∂disorderLaw (d+2) μ.maxDegree) ≤
    expectedUncoveredGibbsMass d μ β a ep τ +
      (disorderLaw (d+2) μ.maxDegree).real {J | m+L < sourceSphereMaximum d μ 1 J} +
      (disorderLaw (d+2) μ.maxDegree).real
        {J | partition (d+2) β (field (mixtureCoefficients μ) J) < η*A} +
      ((∫⁻ J, originalEnergyMarkedCount d μ β
        (Icc ((d+2:ℕ)*(ep-τ)) (m-L)) (Ico a 1) J
        ∂disorderLaw (d+2) μ.maxDegree).toReal +
      (∫⁻ J, originalEnergyMarkedCount d μ β
        (Icc (m-L) (m+L)) (Ico a 1 \ Icc (q-b) (q+b)) J
        ∂disorderLaw (d+2) μ.maxDegree).toReal)/(η*A) := by
  let P := disorderLaw (d+2) μ.maxDegree
  let X (J : Disorder (d+2) μ.maxDegree) :=
    (gibbsLaw (d+2) β (field (mixtureCoefficients μ) J)).real
      (originalEnergyBandUnion d μ m L q b J)ᶜ
  let U := uncoveredGibbsMass d μ β a ep τ
  let D := originalEnergyMarkedCount d μ β
    (Icc ((d+2:ℕ)*(ep-τ)) (m-L)) (Ico a 1)
  let W := originalEnergyMarkedCount d μ β
    (Icc (m-L) (m+L)) (Ico a 1 \ Icc (q-b) (q+b))
  let Emax := {J : Disorder (d+2) μ.maxDegree | m+L < sourceSphereMaximum d μ 1 J}
  let Eden := {J : Disorder (d+2) μ.maxDegree |
    partition (d+2) β (field (mixtureCoefficients μ) J) < η*A}
  let R (J : Disorder (d+2) μ.maxDegree) :=
    U J+Emax.indicator (fun _ => (1:ℝ)) J+Eden.indicator (fun _ => (1:ℝ)) J+
      ((D J).toReal+(W J).toReal)/(η*A)
  have hηA : 0 < η*A := mul_pos hη hA
  have hDm : AEMeasurable D P :=
    capture_original_marked_count_aemeasurable d μ β measurableSet_Icc measurableSet_Ico
  have hWm : AEMeasurable W P := capture_original_marked_count_aemeasurable d μ β
    measurableSet_Icc (measurableSet_Ico.diff measurableSet_Icc)
  have hDi : Integrable (fun J => (D J).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hDm hDeep
  have hWi : Integrable (fun J => (W J).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hWm hAngular
  have hUi : Integrable U P := uncoveredGibbsMass_integrable d μ β a ep τ
  have hMax : MeasurableSet Emax :=
    measurableSet_lt measurable_const (sourceSphereMaximum_continuous d μ 1).measurable
  have hDen : MeasurableSet Eden :=
    measurableSet_lt (partition_measurable (mixtureCoefficients μ) β) measurable_const
  have hMi : Integrable (Emax.indicator (fun _ => (1:ℝ))) P :=
    (integrable_const 1).indicator hMax
  have hNi : Integrable (Eden.indicator (fun _ => (1:ℝ))) P :=
    (integrable_const 1).indicator hDen
  have hDWi := (hDi.add hWi).div_const (η*A)
  have hRi : Integrable R P := ((hUi.add hMi).add hNi).add hDWi
  have hpoint : ∀ᵐ J ∂P, X J ≤ R J := by
    filter_upwards [originalEnergyCriticalSet_finite_ae d μ] with J hfinite
    let π := gibbsLaw (d+2) β (field (mixtureCoefficients μ) J)
    let : IsProbabilityMeasure π :=
      gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
    have hX : X J ≤ 1 := measureReal_le_one
    have hU : 0 ≤ U J := (uncoveredGibbsMass_mem_unit d μ β a ep τ J).1
    have hD : 0 ≤ (D J).toReal := ENNReal.toReal_nonneg
    have hW : 0 ≤ (W J).toReal := ENNReal.toReal_nonneg
    have hM : 0 ≤ Emax.indicator (fun _ => (1:ℝ)) J :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hN : 0 ≤ Eden.indicator (fun _ => (1:ℝ)) J :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hquot : 0 ≤ ((D J).toReal+(W J).toReal)/(η*A) := by positivity
    by_cases hJmax : J ∈ Emax
    · have hone : Emax.indicator (fun _ => (1:ℝ)) J = 1 :=
        Set.indicator_of_mem hJmax _
      dsimp only [R]
      linarith
    by_cases hJden : J ∈ Eden
    · have hone : Eden.indicator (fun _ => (1:ℝ)) J = 1 :=
        Set.indicator_of_mem hJden _
      dsimp only [R]
      linarith
    have hZ : η*A ≤ partition (d+2) β (field (mixtureCoefficients μ) J) :=
      le_of_not_gt hJden
    have hMaximum : sourceSphereMaximum d μ 1 J ≤ m+L := le_of_not_gt hJmax
    have hc : centerCoefficients (mixtureCoefficients μ) 1 = mixtureCoefficients μ := by
      funext k
      simp [centerCoefficients]
    obtain ⟨v,hv,_,hmaxv,heqv⟩ := sourceSphereMaximum_attained d μ 1 J
    rw [hc] at hmaxv heqv
    have hmaxfield (u : Vector (d+2)) (hu : ‖u‖^2=(d+2:ℕ)) :
        field (mixtureCoefficients μ) J u ≤ m+L := by
      have hh := hmaxv hu
      rw [←heqv] at hh
      exact hh.trans hMaximum
    have hCompare := original_gibbs_band_complement_le d hd μ β a ep τ m L q b
      J hfinite hmaxfield
    have hDiv := div_le_div_of_nonneg_left (add_nonneg hD hW) hηA hZ
    dsimp only [X,R,U,D,W] at *
    linarith
  have hDeq := integral_toReal hDm (ae_lt_top' hDm hDeep)
  have hWeq := integral_toReal hWm (ae_lt_top' hWm hAngular)
  calc
    _ ≤ ∫ J, R J ∂P := integral_mono_ae hBandInt hRi hpoint
    _ = _ := by
      change (∫ J, (((U+Emax.indicator (fun _ => (1:ℝ)))+
        Eden.indicator (fun _ => (1:ℝ)))+
        (fun J => ((fun J => (D J).toReal)+(fun J => (W J).toReal)) J/(η*A))) J ∂P) = _
      rw [integral_add' ((hUi.add hMi).add hNi) hDWi,
        integral_add' (hUi.add hMi) hNi,integral_add' hUi hMi,
        integral_div,integral_add' hDi hWi,integral_indicator_const 1 hMax,
        integral_indicator_const 1 hDen,hDeq,hWeq]
      simp only [smul_eq_mul, mul_one]
      rfl

end SlowEquilibration.SourcePureCaptureExpectationBound
