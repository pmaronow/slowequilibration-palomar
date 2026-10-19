-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPLatitudePathJets
public import SlowEquilibration.SphericalTAPPosteriorBallRegularity
public import SlowEquilibration.SourcePhysicalPairPhysicalPosteriorRegularity

@[expose] public section

/-! Curvature of the original conditioned Hamiltonian along the literal
latitude chart. The only regularity hypothesis is membership in the proved
posterior tensor event. -/

namespace SlowEquilibration.SphericalTAPPosteriorLatitudeRegularity
noncomputable section
open Set
open MeasureTheory
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalMarkedWindows
open SlowEquilibration.PairConditionalDeterminantMoments
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.WholeFieldRegression
open NormalizedPairObservations PairObservationTargets
open SlowEquilibration.SphericalTAPLatitudePathJets
open SlowEquilibration.SphericalTAPPosteriorBallRegularity
set_option autoImplicit false

theorem field_posterior_latitude_second_bound
    {n P : ℕ} (hn : 1 ≤ n) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) {K : ℝ} (hK : 0 ≤ K)
    (hJ : J ∈ sourcePosteriorOrderedRegularity K)
    (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ y, inner ℝ (e y) u = 0)
    (x : Vector n) (hx : ‖x‖^2 = (n:ℝ))
    {a r B : ℝ} (ha : a ∈ Icc (-r) r)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hB : ∀ t ∈ Icc (-r) r,
      |iteratedDeriv 2 transverseLatitudeRadius t| ≤ B) :
    |iteratedDeriv 2 (fun t => field c J (latitudeMap u e t x)) a| ≤
      posteriorDerivativeConstant c K *
        ((1/(1-r^2))^2+B) * ((n+1:ℕ):ℝ) := by
  have haopen : a ∈ Ioo (-1:ℝ) 1 := by
    constructor <;> linarith [ha.1,ha.2,hr1]
  have hcurve : ContDiffAt ℝ 2 (fun t => latitudeMap u e t x) a := by
    have hfun : (fun t => latitudeMap u e t x) =
        physicalLatitudePoint u
          (Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • e x) := by
      funext t
      exact latitudeMap_eq_physicalLatitudePoint u e x t
    rw [hfun]
    exact physicalLatitudePoint_contDiffAt u _ haopen
  have hball : ‖latitudeMap u e a x‖ ≤ Real.sqrt ((n+1:ℕ):ℝ) := by
    have hsq := latitudeMap_norm_sq hn u hu e he (abs_lt.mpr haopen).le x hx
    exact (SphericalAging.LandscapeDerivatives.sphere_norm _ hsq).le
  have hspeed : ‖deriv (fun t => latitudeMap u e t x) a‖ ≤
      (1/(1-r^2))*Real.sqrt ((n+1:ℕ):ℝ) := by
    convert physicalLatitudeMap_speed_bound hn u hu e he x hx
      haopen hr0 hr1 (abs_le.mpr ha) using 1
    ring
  have hacc := latitudeMap_acceleration_bound hn u e x hx ha hr1 hB
  exact field_posterior_curve_second_bound (by omega) c J hK hJ
    (fun t => latitudeMap u e t x) a hcurve hball hspeed hacc

/-- One constant controls every center, transverse spin, and latitude in a
fixed compact interior strip, on the posterior tensor event. -/
theorem field_posterior_latitude_uniform_bound
    {P : ℕ} (c : Degree P → ℝ) {K r : ℝ}
    (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (J : Disorder (n+1) P),
      J ∈ sourcePosteriorOrderedRegularity K →
      ∀ (u : Vector (n+1)), ‖u‖^2 = ((n+1:ℕ):ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
        (∀ y, inner ℝ (e y) u = 0) →
      ∀ (x : Vector n), ‖x‖^2 = (n:ℝ) →
      ∀ a ∈ Icc (-r) r,
      |iteratedDeriv 2 (fun t => field c J (latitudeMap u e t x)) a| ≤
        C * ((n+1:ℕ):ℝ) := by
  obtain ⟨B, hB0, hB⟩ := transverseLatitudeRadius_second_uniform hr1
  let C := posteriorDerivativeConstant c K * ((1/(1-r^2))^2+B)
  have hden : 0 < 1-r^2 := by nlinarith [hr0,hr1]
  have hC : 0 < C := by
    dsimp [C]
    have hfactor : 0 < (1/(1-r^2))^2+B := by positivity
    exact mul_pos (posteriorDerivativeConstant_pos c hK) hfactor
  refine ⟨C, hC, ?_⟩
  intro n hn J hJ u hu e he x hx a ha
  exact field_posterior_latitude_second_bound hn c J hK hJ
    u hu e he x hx ha hr0 hr1 hB

/-- Under the actual mixed critical-point coefficient posterior, a single
measurable event has exponentially small failure probability and controls
the original Hamiltonian's second latitude derivative uniformly. -/
theorem source_mixed_posterior_latitude_regular
    (μ : FiniteMixture) {Q M r : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (n m : ℕ), 1 ≤ n →
      ∀ (u : Vector (n+1)), ‖u‖^2 = ((n+1:ℕ):ℝ) →
      ∀ (f : Fin m → Vector (n+1)), Orthonormal ℝ f →
        (∀ i, inner ℝ (f i) u = 0) →
      ∀ (h k : ℝ), |h| ≤ M → |k| ≤ M →
        let good := sourcePosteriorOrderedRegularity
          (N := n+1) (P := μ.maxDegree) K
        MeasurableSet good ∧
        (coefficientKernel
          (singleMixedObservation
            (centerCoefficients (mixtureCoefficients μ) Q) u f)
          (mixedPointTarget (n+1) m h k)).real goodᶜ ≤
          (Fintype.card (Degree μ.maxDegree):ℝ) *
            Real.exp (-((n+1:ℕ):ℝ)/2) ∧
        ∀ J ∈ good,
          ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
            (∀ y, inner ℝ (e y) u = 0) →
          ∀ (x : Vector n), ‖x‖^2 = (n:ℝ) →
          ∀ a ∈ Icc (-r) r,
          |iteratedDeriv 2
            (fun t => field (mixtureCoefficients μ) J
              (latitudeMap u e t x)) a| ≤ C*((n+1:ℕ):ℝ) := by
  obtain ⟨K, hK, htail⟩ :=
    source_mixed_posterior_orderedRegularity μ hQ hnp hM
  obtain ⟨C, hC, hfield⟩ := field_posterior_latitude_uniform_bound
    (mixtureCoefficients μ) hK.le hr0 hr1
  refine ⟨K, C, hK, hC, ?_⟩
  intro n m hn u hu f hf htan h k hh hk
  dsimp only
  refine ⟨sourcePosteriorOrderedRegularity_measurable (n+1)
    μ.maxDegree K, ?_, ?_⟩
  · exact htail (n+1) m (by omega) u hu f hf htan h k hh hk
  · intro J hJ e he x hx a ha
    exact hfield n hn J hJ u hu e he x hx a ha

/-- The compatible-mark pure posterior uses the value-only observation;
the same event uniformly controls its literal latitude curves. -/
theorem source_value_posterior_latitude_regular
    (μ : FiniteMixture) {Q M r : ℝ} (hQ : 0 < Q)
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (n m : ℕ), 1 ≤ n →
      ∀ (u : Vector (n+1)), ‖u‖^2 = ((n+1:ℕ):ℝ) →
      ∀ (f : Fin m → Vector (n+1)), Orthonormal ℝ f →
        (∀ i, inner ℝ (f i) u = 0) →
      ∀ h : ℝ, |h| ≤ M →
        let good := sourcePosteriorOrderedRegularity
          (N := n+1) (P := μ.maxDegree) K
        MeasurableSet good ∧
        (coefficientKernel
          (singleValueObservation
            (centerCoefficients (mixtureCoefficients μ) Q) u f)
          (valuePointTarget (n+1) m h)).real goodᶜ ≤
          (Fintype.card (Degree μ.maxDegree):ℝ) *
            Real.exp (-((n+1:ℕ):ℝ)/2) ∧
        ∀ J ∈ good,
          ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
            (∀ y, inner ℝ (e y) u = 0) →
          ∀ (x : Vector n), ‖x‖^2 = (n:ℝ) →
          ∀ a ∈ Icc (-r) r,
          |iteratedDeriv 2
            (fun t => field (mixtureCoefficients μ) J
              (latitudeMap u e t x)) a| ≤ C*((n+1:ℕ):ℝ) := by
  obtain ⟨K, hK, htail⟩ :=
    source_value_posterior_orderedRegularity μ hQ hM
  obtain ⟨C, hC, hfield⟩ := field_posterior_latitude_uniform_bound
    (mixtureCoefficients μ) hK.le hr0 hr1
  refine ⟨K, C, hK, hC, ?_⟩
  intro n m hn u hu f hf htan h hh
  dsimp only
  refine ⟨sourcePosteriorOrderedRegularity_measurable (n+1)
    μ.maxDegree K, ?_, ?_⟩
  · exact htail (n+1) m (by omega) u hu f hf htan h hh
  · intro J hJ e he x hx a ha
    exact hfield n hn J hJ u hu e he x hx a ha

/-- The same uniform curvature event under the manuscript's actual
mixed critical-point law, rather than an arbitrary observation frame. -/
theorem source_mixed_conditioned_latitude_regular
    (μ : FiniteMixture) {Q M r : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ (h k : ℝ), |h| ≤ M → |k| ≤ M →
        let good := sourcePosteriorOrderedRegularity
          (N := n+1) (P := μ.maxDegree) K
        MeasurableSet good ∧
        (mixedConditionedLaw
          (centerCoefficients (mixtureCoefficients μ) Q) u hu
          (WithLp.toLp 2 ![h,k])).real goodᶜ ≤
          (Fintype.card (Degree μ.maxDegree):ℝ) *
            Real.exp (-((n+1:ℕ):ℝ)/2) ∧
        ∀ J ∈ good,
          ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
            (∀ y, inner ℝ (e y) u = 0) →
          ∀ (x : Vector n), ‖x‖^2 = (n:ℝ) →
          ∀ a ∈ Icc (-r) r,
          |iteratedDeriv 2
            (fun t => field (mixtureCoefficients μ) J
              (latitudeMap u e t x)) a| ≤ C*((n+1:ℕ):ℝ) := by
  obtain ⟨K, hK, htail⟩ :=
    source_mixed_physical_posterior_orderedRegularity μ hQ hnp hM
  obtain ⟨C, hC, hfield⟩ := field_posterior_latitude_uniform_bound
    (mixtureCoefficients μ) hK.le hr0 hr1
  refine ⟨K, C, hK, hC, ?_⟩
  intro n hn u hu h k hh hk
  dsimp only
  refine ⟨sourcePosteriorOrderedRegularity_measurable (n+1)
    μ.maxDegree K, htail n u hu h k hh hk, ?_⟩
  intro J hJ e he x hx a ha
  exact hfield n hn J hJ u hu e he x hx a ha

/-- The original compatible pure-mark law is a value-only posterior, with
the same uniform regularity conclusion. -/
theorem source_value_conditioned_latitude_regular
    (μ : FiniteMixture) {Q M r : ℝ} (hQ : 0 < Q)
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ h : ℝ, |h| ≤ M →
        let good := sourcePosteriorOrderedRegularity
          (N := n+1) (P := μ.maxDegree) K
        MeasurableSet good ∧
        (valueConditionedLaw
          (centerCoefficients (mixtureCoefficients μ) Q) u hu h).real goodᶜ ≤
          (Fintype.card (Degree μ.maxDegree):ℝ) *
            Real.exp (-((n+1:ℕ):ℝ)/2) ∧
        ∀ J ∈ good,
          ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
            (∀ y, inner ℝ (e y) u = 0) →
          ∀ (x : Vector n), ‖x‖^2 = (n:ℝ) →
          ∀ a ∈ Icc (-r) r,
          |iteratedDeriv 2
            (fun t => field (mixtureCoefficients μ) J
              (latitudeMap u e t x)) a| ≤ C*((n+1:ℕ):ℝ) := by
  obtain ⟨K, hK, htail⟩ :=
    source_value_physical_posterior_orderedRegularity μ hQ hM
  obtain ⟨C, hC, hfield⟩ := field_posterior_latitude_uniform_bound
    (mixtureCoefficients μ) hK.le hr0 hr1
  refine ⟨K, C, hK, hC, ?_⟩
  intro n hn u hu h hh
  dsimp only
  refine ⟨sourcePosteriorOrderedRegularity_measurable (n+1)
    μ.maxDegree K, htail n u hu h hh, ?_⟩
  intro J hJ e he x hx a ha
  exact hfield n hn J hJ u hu e he x hx a ha

/-- Literal bad-curvature probability for the original mixed conditioned
Hamiltonian on a complete latitude strip and transverse sphere. -/
theorem source_mixed_conditioned_latitude_failure
    (μ : FiniteMixture) {Q M r : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ (h k : ℝ), |h| ≤ M → |k| ≤ M →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
        (∀ y, inner ℝ (e y) u = 0) →
        (mixedConditionedLaw
          (centerCoefficients (mixtureCoefficients μ) Q) u hu
          (WithLp.toLp 2 ![h,k])).real
          {J | ∃ x : Vector n, ‖x‖^2 = (n:ℝ) ∧
            ∃ a ∈ Icc (-r) r,
              C*((n+1:ℕ):ℝ) <
                |iteratedDeriv 2
                  (fun t => field (mixtureCoefficients μ) J
                    (latitudeMap u e t x)) a|} ≤
          (Fintype.card (Degree μ.maxDegree):ℝ) *
            Real.exp (-((n+1:ℕ):ℝ)/2) := by
  obtain ⟨K, C, hK, hC, hall⟩ :=
    source_mixed_conditioned_latitude_regular μ hQ hnp hM hr0 hr1
  refine ⟨C, hC, ?_⟩
  intro n hn u hu h k hh hk e he
  let : IsProbabilityMeasure
      (mixedConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu
        (WithLp.toLp 2 ![h,k])) := by
    unfold mixedConditionedLaw
    infer_instance
  obtain ⟨_, htail, hbound⟩ := hall n hn u hu h k hh hk
  have hsub :
      {J : Disorder (n+1) μ.maxDegree |
        ∃ x : Vector n, ‖x‖^2 = (n:ℝ) ∧
          ∃ a ∈ Icc (-r) r,
            C*((n+1:ℕ):ℝ) <
              |iteratedDeriv 2
                (fun t => field (mixtureCoefficients μ) J
                  (latitudeMap u e t x)) a|} ⊆
      (sourcePosteriorOrderedRegularity
        (N := n+1) (P := μ.maxDegree) K)ᶜ := by
    intro J hbad hgood
    obtain ⟨x, hx, a, ha, hstrict⟩ := hbad
    exact not_lt_of_ge (hbound J hgood e he x hx a ha) hstrict
  exact (measureReal_mono hsub).trans htail

/-- Literal bad-curvature probability under the compatible pure-mark
value-only posterior. -/
theorem source_value_conditioned_latitude_failure
    (μ : FiniteMixture) {Q M r : ℝ} (hQ : 0 < Q)
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ h : ℝ, |h| ≤ M →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
        (∀ y, inner ℝ (e y) u = 0) →
        (valueConditionedLaw
          (centerCoefficients (mixtureCoefficients μ) Q) u hu h).real
          {J | ∃ x : Vector n, ‖x‖^2 = (n:ℝ) ∧
            ∃ a ∈ Icc (-r) r,
              C*((n+1:ℕ):ℝ) <
                |iteratedDeriv 2
                  (fun t => field (mixtureCoefficients μ) J
                    (latitudeMap u e t x)) a|} ≤
          (Fintype.card (Degree μ.maxDegree):ℝ) *
            Real.exp (-((n+1:ℕ):ℝ)/2) := by
  obtain ⟨K, C, hK, hC, hall⟩ :=
    source_value_conditioned_latitude_regular μ hQ hM hr0 hr1
  refine ⟨C, hC, ?_⟩
  intro n hn u hu h hh e he
  let : IsProbabilityMeasure
      (valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu h) := by
    unfold valueConditionedLaw
    infer_instance
  obtain ⟨_, htail, hbound⟩ := hall n hn u hu h hh
  have hsub :
      {J : Disorder (n+1) μ.maxDegree |
        ∃ x : Vector n, ‖x‖^2 = (n:ℝ) ∧
          ∃ a ∈ Icc (-r) r,
            C*((n+1:ℕ):ℝ) <
              |iteratedDeriv 2
                (fun t => field (mixtureCoefficients μ) J
                  (latitudeMap u e t x)) a|} ⊆
      (sourcePosteriorOrderedRegularity
        (N := n+1) (P := μ.maxDegree) K)ᶜ := by
    intro J hbad hgood
    obtain ⟨x, hx, a, ha, hstrict⟩ := hbad
    exact not_lt_of_ge (hbound J hgood e he x hx a ha) hstrict
  exact (measureReal_mono hsub).trans htail

end
end SlowEquilibration.SphericalTAPPosteriorLatitudeRegularity
