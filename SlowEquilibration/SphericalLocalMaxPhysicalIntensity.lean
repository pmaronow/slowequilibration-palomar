-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLocalMaxCount
public import SlowEquilibration.SphericalCountRectangles

/-! The source energy-coordinate intensity: energy is unnormalized while
the radial multiplier is normalized. The exact Jacobian removes one factor N. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalSequentialRegression
open GOEMaximumDeterminant GOERawMoments GOEAsymptotics
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma maximumMean_measurable (n N : ℕ) (b : ℝ) : Measurable (maximumMean n N b) := by
  have hd : Continuous (fun p : ℝ × Matrix (Fin (n+1)) (Fin (n+1)) ℝ => matrixAbsoluteDet n p.1 p.2) :=
    ((continuous_fst.smul continuous_const).sub continuous_snd).matrix_det.abs
  have hs : MeasurableSet {p : ℝ × Matrix (Fin (n+1)) (Fin (n+1)) ℝ | eigenvalues n p.2 0 < p.1} :=
    measurableSet_lt (((measurable_pi_apply 0).comp (eigenvalues_measurable n)).comp measurable_snd) measurable_fst
  have hf : Measurable (fun p : ℝ × Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
      if eigenvalues n p.2 0 < p.1 then matrixAbsoluteDet n p.1 p.2 else 0) :=
    Measurable.ite hs hd.measurable measurable_const
  have hm := (hf.stronglyMeasurable.integral_prod_right' (ν := goeLaw (n+1) N b)).measurable
  convert hm using 1
  funext k
  rw [maximumMean,← integral_indicator (maximumEvent_measurable n k)]
  rfl

lemma mixedNegativeIntensity_measurable (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Measurable (mixedNegativeIntensity n μ Q) := by
  exact (measurable_const.mul (physicalScorePdf_measurable (n+2) μ Q)).mul
    (((maximumMean_measurable n (n+2) (Q^2 * μ.xi2 Q)).comp
      ((EuclideanSpace.proj (1 : Fin 2)).continuous.measurable)).ennreal_ofReal)

/-- Rescaling a literal scalar Lebesgue window, with its exact Jacobian. -/
lemma setLIntegral_positive_rescale (a : ℝ) (ha : 0 < a) (I : Set ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in (fun t : ℝ => a*t) ⁻¹' I, f t) =
      ∫⁻ H in I, ENNReal.ofReal a⁻¹ * f (H/a) := by
  have hmp : MeasurePreserving (fun t : ℝ => a*t) volume (ENNReal.ofReal a⁻¹ • volume) :=
    ⟨measurable_const_mul a,by simpa only [abs_of_pos (inv_pos.mpr ha)] using Real.map_volume_mul_left ha.ne'⟩
  have he := hmp.setLIntegral_comp_preimage_emb (Homeomorph.mulLeft₀ a ha.ne').measurableEmbedding
    (fun H => f (H/a)) I
  simp only [mul_div_cancel_left₀ _ ha.ne'] at he
  rw [Measure.restrict_smul,lintegral_smul_measure] at he
  exact he.trans (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

def mixedLocalMaxPhysicalIntensity (n : ℕ) (μ : FiniteMixture) (Q H k : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹ *
    mixedNegativeIntensity n μ Q (WithLp.toLp 2 ![H/(n+2 : ℕ),k])

def mixedCriticalPhysicalIntensity (n : ℕ) (μ : FiniteMixture) (Q H k : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹ *
    mixedCriticalIntensity n μ Q (WithLp.toLp 2 ![H/(n+2 : ℕ),k])

/-- The energy window is a window of the actual unnormalized field. -/
def physicalEnergyWindow (N : ℕ) (I U : Set ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangularScoreWindow ((fun h : ℝ => (N:ℝ)*h) ⁻¹' I) U

lemma actualScore_mem_physicalEnergyWindow {N P : ℕ} (hN : N ≠ 0) (c : Degree P → ℝ)
    (J : Disorder N P) (x : Vector N) (I U : Set ℝ) :
    actualScore c J x ∈ physicalEnergyWindow N I U ↔ field c J x ∈ I ∧ actualScore c J x 1 ∈ U := by
  have hval : (N:ℝ) * actualScore c J x 0 = field c J x := by
    change (N:ℝ) * ((N:ℝ)⁻¹ * scoreCLM c x (euclideanDisorder J) 0) = _
    rw [scoreCLM_apply_zero,unpack_euclideanDisorder,mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr hN)]
    simp only [jet,iteratedFDeriv_zero_apply]
  change (N:ℝ) * actualScore c J x 0 ∈ I ∧ actualScore c J x 1 ∈ U ↔ _
  rw [hval]

/-- Genuine local maxima, integrated with respect to ordinary unnormalized
energy and normalized radial multiplier, exactly as in the source intensity. -/
theorem actual_mixed_localMax_physical_intensity (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (I U : Set ℝ) (hI : MeasurableSet I) (hU : MeasurableSet U) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualLocalMaxCount (n+1) c (physicalEnergyWindow (n+2) I U) J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ H in I, ∫⁻ k in U, mixedLocalMaxPhysicalIntensity n μ Q H k := by
  dsimp only
  have hw : MeasurableSet (physicalEnergyWindow (n+2) I U) :=
    rectangularScoreWindow_measurable _ _ (hI.preimage (measurable_const_mul ((n+2 : ℕ):ℝ))) hU
  rw [(actual_mixed_localMax_count_intensity n μ hQ hnp _ hw).2]
  rw [physicalEnergyWindow,lintegral_rectangularScoreWindow _ _ _ (mixedNegativeIntensity_measurable n μ Q)]
  rw [setLIntegral_positive_rescale (n+2 : ℕ) (by positivity)]
  apply lintegral_congr
  intro H
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

lemma inverse_dimension_prefactor (n : ℕ) (c T : ℝ) :
    ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹ * ENNReal.ofReal (c*(n+2 : ℕ)*Real.exp T) =
      ENNReal.ofReal (c*Real.exp T) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The exact source mixed intensity bound: no power of N remains when
energy is unnormalized. Constants are uniform in every energy and the exterior
radial interval; the middle inequality compares genuine local maxima to all
genuine critical points. -/
theorem mixed_localMax_physical_prefactors (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) {g Z : ℝ} (hg : 0 < g) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ e k : ℝ,
      k ∈ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z →
      ENNReal.ofReal (c*Real.exp ((n+2 : ℕ)*markedComplexity μ Q (WithLp.toLp 2 ![e,k]))) ≤
        mixedLocalMaxPhysicalIntensity n μ Q ((n+2 : ℕ)*e) k ∧
      mixedLocalMaxPhysicalIntensity n μ Q ((n+2 : ℕ)*e) k ≤
        mixedCriticalPhysicalIntensity n μ Q ((n+2 : ℕ)*e) k ∧
      mixedCriticalPhysicalIntensity n μ Q ((n+2 : ℕ)*e) k ≤
        ENNReal.ofReal (C*Real.exp ((n+2 : ℕ)*markedComplexity μ Q (WithLp.toLp 2 ![e,k]))) := by
  obtain ⟨c,C,hc,hC,hm⟩ := actual_mixed_negative_intensity_prefactors μ hQ hnp (Z := Z) hg
  obtain ⟨a,B,ha,hB,hall⟩ := actual_mixed_intensity_prefactors μ hQ hnp (Z := Z) hg
  refine ⟨c,B,hc,hB,?_⟩
  filter_upwards [hm,mixedNegativeIntensity_comparison μ hQ (Z := Z) hg] with n hn hcomp
  intro e k hk
  have he : (((n+2 : ℕ):ℝ)*e)/(n+2 : ℕ)=e := mul_div_cancel_left₀ _ (by positivity)
  simp only [mixedLocalMaxPhysicalIntensity,mixedCriticalPhysicalIntensity,he]
  have h1 := mul_le_mul_right (hn (WithLp.toLp 2 ![e,k]) hk).1 (ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹)
  have h2 := mul_le_mul_right (hcomp (WithLp.toLp 2 ![e,k]) hk).2 (ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹)
  have h3 := mul_le_mul_right (hall n (WithLp.toLp 2 ![e,k]) hk).2 (ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹)
  rw [inverse_dimension_prefactor] at h1 h3
  exact ⟨h1,h2,h3⟩

end
end SlowEquilibration.SphericalMarkedWindows
