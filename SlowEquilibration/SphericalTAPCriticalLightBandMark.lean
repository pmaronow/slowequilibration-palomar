-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalLightCountTransfer

@[expose] public section

/-! The literal 12.21 light-band mark on an actual critical center, as a
jointly Borel whole-field and center observable. -/

namespace SlowEquilibration.SphericalTAPCriticalLightBandMark
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCriticalBandSectionBridge
open ConditionedDeterminantMoments
open UnrestrictedConditionedDeterminants GOEPhysicalNormalizedMoments
open SphereHessian
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

/-- Indicator that the physical band around `u` is light relative to the
actual center Hamiltonian value, on the manuscript's `D_N` scale. -/
def sourceLightBandMark (d : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (β mN δ : ℝ) (I : Set ℝ)
    (J : Disorder (d+2) μ.maxDegree) (u : Vector (d+2)) : ℝ≥0∞ :=
  if overlapRestrictedPartition (mixtureCoefficients μ) β I (J,u) <
      δ * sourceCriticalBandScale (d+1) μ hQ β mN *
        Real.exp (β*(field (centerCoefficients (mixtureCoefficients μ) Q) J u-mN))
  then 1 else 0

theorem sourceLightBandMark_measurable
    (d : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (β mN δ : ℝ) (I : Set ℝ) (hI : MeasurableSet I) :
    Measurable (fun z : Disorder (d+2) μ.maxDegree × Vector (d+2) =>
      sourceLightBandMark d μ hQ β mN δ I z.1 z.2) := by
  unfold sourceLightBandMark
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_lt
    (overlapRestrictedPartition_measurable (mixtureCoefficients μ) β hI)
    (measurable_const.mul
      ((Real.measurable_exp.comp
        ((measurable_const.mul
          ((field_jointContinuous (centerCoefficients
            (mixtureCoefficients μ) Q)).measurable.sub measurable_const))))))

/-- Conditioning on the actual value/radial score pins the center energy to
`N e`; the light-band mark is therefore the fixed-mark Palm bad event. -/
theorem sourceLightBandMark_mixed_conditional_ae
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : Q ∈ Ioo (0:ℝ) 1)
    (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (z : EuclideanSpace ℝ (Fin 2))
    (β mN δ : ℝ) (I : Set ℝ) :
    ∀ᵐ J ∂mixedLaw μ Q u hu z,
      sourceLightBandMark d μ hQ β mN δ I J u =
        if partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u I) <
          δ*sourceCriticalBandScale (d+1) μ hQ β mN *
            Real.exp (β*(((d+2:ℕ):ℝ)*z 0-mN))
        then 1 else 0 := by
  have hscore : ∀ᵐ J ∂mixedLaw μ Q u hu z,
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u = z :=
    mixedConditioned_score_ae μ hQ.1 hnp u hu z
  filter_upwards [hscore] with J hz
  have hN : (((d+2:ℕ):ℝ)) ≠ 0 := by positivity
  have hv : field (centerCoefficients (mixtureCoefficients μ) Q) J u /
      (((d+2:ℕ):ℝ)) = z 0 := by
    rw [← actualScore_value_eq]
    exact congrArg (fun b : EuclideanSpace ℝ (Fin 2) => b 0) hz
  have hf : field (centerCoefficients (mixtureCoefficients μ) Q) J u =
      (((d+2:ℕ):ℝ))*z 0 := by
    have hh := (div_eq_iff hN).mp hv
    simpa only [mul_comm] using hh
  unfold sourceLightBandMark overlapRestrictedPartition
  rw [hf]
  rfl

/-- A real determinant-weighted Palm ratio bound becomes the precise
nonnegative marked intensity inequality required by Kac--Rice. -/
theorem palm_ratio_to_lintegral_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (D : Ω → ℝ)
    (hD : Integrable D ν) (hD0 : ∀ J, 0 ≤ D J)
    (A : Set Ω) (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hMean : 0 < ∫ J, D J ∂ν)
    (hRatio : (∫ J in A, D J ∂ν) / (∫ J, D J ∂ν) ≤ ε) :
    (∫⁻ J, ENNReal.ofReal (D J) * (if J ∈ A then 1 else 0) ∂ν) ≤
      ENNReal.ofReal ε * (∫⁻ J, ENNReal.ofReal (D J) ∂ν) := by
  classical
  have hnum : (∫⁻ J, ENNReal.ofReal (D J) *
      (if J ∈ A then 1 else 0) ∂ν) =
      ENNReal.ofReal (∫ J in A, D J ∂ν) := by
    rw [show (fun J => ENNReal.ofReal (D J) *
        (if J ∈ A then 1 else 0)) =
        A.indicator (fun J => ENNReal.ofReal (D J)) by
          funext J
          by_cases hJ : J ∈ A <;> simp [hJ]]
    rw [lintegral_indicator hA]
    exact (ofReal_integral_eq_lintegral_ofReal hD.restrict
      (.of_forall hD0)).symm
  have hden : (∫⁻ J, ENNReal.ofReal (D J) ∂ν) =
      ENNReal.ofReal (∫ J, D J ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hD (.of_forall hD0)).symm
  have hreal := (div_le_iff₀ hMean).mp hRatio
  rw [hnum,hden,← ENNReal.ofReal_mul hε]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The fixed-mark source Palm lower-tail bound applies to the literal
light-band mark appearing in the global Kac--Rice count. -/
theorem sourceLightBandMark_mixed_local_intensity_le
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : Q ∈ Ioo (0:ℝ) 1)
    (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (z : EuclideanSpace ℝ (Fin 2))
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < z 1)
    (β mN δ : ℝ) (I : Set ℝ) (hI : MeasurableSet I)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hRatio :
      (∫ J in {J | partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u I) <
        δ*sourceCriticalBandScale (d+1) μ hQ β mN *
          Real.exp (β*(((d+2:ℕ):ℝ)*z 0-mN))},
        intrinsicDet μ Q u J ∂mixedLaw μ Q u hu z) /
      (∫ J, intrinsicDet μ Q u J ∂mixedLaw μ Q u hu z) ≤ ε) :
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian
      (field (centerCoefficients (mixtureCoefficients μ) Q) J) u).det| *
      sourceLightBandMark d μ hQ β mN δ I J u
        ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q)
          u hu z) ≤
    ENNReal.ofReal ε *
      (∫⁻ J, ENNReal.ofReal |(intrinsicHessian
        (field (centerCoefficients (mixtureCoefficients μ) Q) J) u).det|
          ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q)
            u hu z) := by
  let A : Set (Disorder (d+2) μ.maxDegree) :=
    {J | partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u I) <
      δ*sourceCriticalBandScale (d+1) μ hQ β mN *
        Real.exp (β*(((d+2:ℕ):ℝ)*z 0-mN))}
  have hA : MeasurableSet A := by
    apply measurableSet_lt
    · exact SphericalTAPCriticalBandSectionBridge.sourceBandPartition_measurable
        (d+1) μ u I hI β
    · exact measurable_const
  have hD : Integrable (intrinsicDet μ Q u) (mixedLaw μ Q u hu z) :=
    mixed_intrinsicDet_integrable μ hQ.1 hnp u hu z
  have hb : 0 < Q^2*μ.xi2 Q :=
    mul_pos (sq_pos_of_pos hQ.1) (μ.xi2_pos hQ.1)
  have hMean : 0 < ∫ J, intrinsicDet μ Q u J ∂mixedLaw μ Q u hu z := by
    rw [determinant_mean_eq_of_law
      (mixed_intrinsicDet_hasLaw μ hQ.1 hnp u hu z)]
    exact physicalMean_pos d 1 hb hk
  have hLocal := palm_ratio_to_lintegral_bound
    (mixedLaw μ Q u hu z) (intrinsicDet μ Q u) hD
    (fun _ => abs_nonneg _) A hA hε hMean hRatio
  have hMark := sourceLightBandMark_mixed_conditional_ae
    d μ hQ hnp u hu z β mN δ I
  have hEq :
      (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) *
        sourceLightBandMark d μ hQ β mN δ I J u
          ∂mixedLaw μ Q u hu z) =
      (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) *
        (if J ∈ A then 1 else 0) ∂mixedLaw μ Q u hu z) := by
    apply lintegral_congr_ae
    filter_upwards [hMark] with J hJ
    rw [hJ]
    rfl
  change (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) *
      sourceLightBandMark d μ hQ β mN δ I J u
      ∂mixedLaw μ Q u hu z) ≤
    ENNReal.ofReal ε *
      (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)
        ∂mixedLaw μ Q u hu z)
  rw [hEq]
  exact hLocal

end
end SlowEquilibration.SphericalTAPCriticalLightBandMark
