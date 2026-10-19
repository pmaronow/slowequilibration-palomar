-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPhysicalBandIntegrability
public import SlowEquilibration.SphericalTAPPosteriorLatitudeRegularity

@[expose] public section

/-! The source posterior latitude regularity event feeds the genuine
physical coarea band lower bound under the exact mixed and value-only
coefficient posteriors. -/

namespace SlowEquilibration.SphericalTAPPosteriorBandLower
noncomputable section
open MeasureTheory Set
open SlowEquilibration.SphericalModel
open SlowEquilibration.PairConditionalDeterminantMoments
open SlowEquilibration.SphericalTAPPhysicalLatitudeSlice
open SlowEquilibration.SphericalTAPPhysicalAngularSlice
open SlowEquilibration.SphericalTAPPhysicalBandIntegrability
open SlowEquilibration.SphericalTAPPosteriorLatitudeRegularity
open SlowEquilibration.SphericalTAPPosteriorBallRegularity
open SlowEquilibration.WholeFieldRegression
open SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalMarkedWindows
open NormalizedPairObservations PairObservationTargets
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The actual physical slice and the `latitudeMap` curve used in the
posterior regularity theorem agree as functions of every real latitude. -/
theorem physicalLatitudeSlice_eq_posteriorLatitudeCurve
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    (x : Vector n) :
    physicalLatitudeSlice n μ u (physicalTransverseAt n u x) J =
      fun a => field (mixtureCoefficients μ) J
        (latitudeMap u (latitudeFrameAt u) a x) := by
  funext a
  have hratio : 0 ≤ (((n+1:ℕ):ℝ)/(n:ℝ)) := by positivity
  unfold physicalLatitudeSlice physicalTransverseAt latitudeMap
  rw [Real.sqrt_mul hratio]
  simp only [smul_smul]
  ring

/-- On the exact mixed critical-point coefficient posterior, an event of
exponentially high probability implies the source-shaped band lower bound.
The regularity event is the actual measurable tensor event, and all
conditioning parameters remain explicit. -/
theorem mixedPosterior_sourceBand_lower
    (μ : FiniteMixture) {Q M r β : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β)
    (I : Set ℝ) (hI : I ⊆ Icc (-r) r) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (n m : ℕ), 2 ≤ n →
      ∀ (u : Vector (n+1)), ‖u‖^2 = ((n+1:ℕ):ℝ) →
      ∀ (f : Fin m → Vector (n+1)), Orthonormal ℝ f →
        (∀ i, inner ℝ (f i) u = 0) →
      ∀ (h k : ℝ), |h| ≤ M → |k| ≤ M →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((n+1:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I →
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
        (latitudeNormalization n).toReal *
          ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
            Real.exp (-(β*C+2/(1-r^2)^2)/2) *
            (1-Q)^((((n-2:ℕ):ℝ))/2) *
            partitionAgainst
              (latitudeLaw u (latitudeFrameAt u) (Real.sqrt Q)) β
              (field (mixtureCoefficients μ) J)) ≤
          partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u I) := by
  obtain ⟨K, C, hK, hC, hgood⟩ :=
    source_mixed_posterior_latitude_regular μ hQ hnp hM hr0 hr1
  refine ⟨K,C,hK,hC,?_⟩
  intro n m hn u hu f hf htan h k hh hk hband
  have hsource := hgood n m (by omega) u hu f hf htan h k hh hk
  dsimp only at hsource ⊢
  refine ⟨hsource.1,hsource.2.1,?_⟩
  intro J hJ
  have hinside : ∀ a ∈ I, |a| ≤ r := by
    intro a ha
    exact abs_le.mpr (hI ha)
  have hfield : ∀ x : Vector n, ‖x‖^2=(n:ℝ) → ∀ a,
      a ∈ I →
      |iteratedDeriv 2
        (physicalLatitudeSlice n μ u (physicalTransverseAt n u x) J) a| ≤
        C*((n+1:ℕ):ℝ) := by
    intro x hx a ha
    rw [physicalLatitudeSlice_eq_posteriorLatitudeCurve n (by omega) μ u J x]
    exact hsource.2.2 J hJ (latitudeFrameAt u)
      (latitudeFrameAt_orthogonal u hu) x hx a (hI ha)
  have hbound := physicalSymmetricLatitudeAveraging_source n hn μ u hu J
    I hr0 hr1 hβ hC.le hband hinside hfield
  simpa only [Real.sq_sqrt hQ.le] using hbound

/-- The same source-shaped lower bound under the compatible value-only
coefficient posterior, with its own exact conditional kernel. -/
theorem valuePosterior_sourceBand_lower
    (μ : FiniteMixture) {Q M r β : ℝ} (hQ : 0 < Q)
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β)
    (I : Set ℝ) (hI : I ⊆ Icc (-r) r) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (n m : ℕ), 2 ≤ n →
      ∀ (u : Vector (n+1)), ‖u‖^2 = ((n+1:ℕ):ℝ) →
      ∀ (f : Fin m → Vector (n+1)), Orthonormal ℝ f →
        (∀ i, inner ℝ (f i) u = 0) →
      ∀ h : ℝ, |h| ≤ M →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((n+1:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I →
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
        (latitudeNormalization n).toReal *
          ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
            Real.exp (-(β*C+2/(1-r^2)^2)/2) *
            (1-Q)^((((n-2:ℕ):ℝ))/2) *
            partitionAgainst
              (latitudeLaw u (latitudeFrameAt u) (Real.sqrt Q)) β
              (field (mixtureCoefficients μ) J)) ≤
          partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u I) := by
  obtain ⟨K, C, hK, hC, hgood⟩ :=
    source_value_posterior_latitude_regular μ hQ hM hr0 hr1
  refine ⟨K,C,hK,hC,?_⟩
  intro n m hn u hu f hf htan h hh hband
  have hsource := hgood n m (by omega) u hu f hf htan h hh
  dsimp only at hsource ⊢
  refine ⟨hsource.1,hsource.2.1,?_⟩
  intro J hJ
  have hinside : ∀ a ∈ I, |a| ≤ r := by
    intro a ha
    exact abs_le.mpr (hI ha)
  have hfield : ∀ x : Vector n, ‖x‖^2=(n:ℝ) → ∀ a,
      a ∈ I →
      |iteratedDeriv 2
        (physicalLatitudeSlice n μ u (physicalTransverseAt n u x) J) a| ≤
        C*((n+1:ℕ):ℝ) := by
    intro x hx a ha
    rw [physicalLatitudeSlice_eq_posteriorLatitudeCurve n (by omega) μ u J x]
    exact hsource.2.2 J hJ (latitudeFrameAt u)
      (latitudeFrameAt_orthogonal u hu) x hx a (hI ha)
  have hbound := physicalSymmetricLatitudeAveraging_source n hn μ u hu J
    I hr0 hr1 hβ hC.le hband hinside hfield
  simpa only [Real.sq_sqrt hQ.le] using hbound

/-- A posterior regularity bound for literal `latitudeMap` curves implies
the physical source band estimate without changing the conditioned field. -/
theorem sourceBand_lower_of_latitudeRegularity
    (n : ℕ) (hn : 2 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (J : Disorder (n+1) μ.maxDegree)
    (I : Set ℝ) {Q r β C : ℝ} (hQ : 0 < Q)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hI : I ⊆ Icc (-r) r)
    (hband : Icc
      (Real.sqrt Q-1/Real.sqrt (((n+1:ℕ):ℝ)))
      (Real.sqrt Q+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I)
    (hreg : ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ y, inner ℝ (e y) u = 0) →
      ∀ (x : Vector n), ‖x‖^2 = (n:ℝ) →
      ∀ a ∈ Icc (-r) r,
      |iteratedDeriv 2
        (fun t => field (mixtureCoefficients μ) J
          (latitudeMap u e t x)) a| ≤ C*((n+1:ℕ):ℝ)) :
    (latitudeNormalization n).toReal *
      ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
        Real.exp (-(β*C+2/(1-r^2)^2)/2) *
        (1-Q)^((((n-2:ℕ):ℝ))/2) *
        partitionAgainst
          (latitudeLaw u (latitudeFrameAt u) (Real.sqrt Q)) β
          (field (mixtureCoefficients μ) J)) ≤
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u I) := by
  have hinside : ∀ a ∈ I, |a| ≤ r := by
    intro a ha
    exact abs_le.mpr (hI ha)
  have hfield : ∀ x : Vector n, ‖x‖^2=(n:ℝ) → ∀ a,
      a ∈ I →
      |iteratedDeriv 2
        (physicalLatitudeSlice n μ u (physicalTransverseAt n u x) J) a| ≤
        C*((n+1:ℕ):ℝ) := by
    intro x hx a ha
    rw [physicalLatitudeSlice_eq_posteriorLatitudeCurve n (by omega) μ u J x]
    exact hreg (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu)
      x hx a (hI ha)
  have hbound := physicalSymmetricLatitudeAveraging_source n hn μ u hu J
    I hr0 hr1 hβ hC hband hinside hfield
  simpa only [Real.sq_sqrt hQ.le] using hbound

/-- The manuscript's actual full-field mixed critical-point conditional
law has an exponentially reliable source-shaped partition lower bound.
This uses `mixedConditionedLaw` directly, rather than an arbitrary frame
posterior or a surrogate observation. -/
theorem mixedConditioned_sourceBand_lower
    (μ : FiniteMixture) {Q M r β : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β)
    (I : Set ℝ) (hI : I ⊆ Icc (-r) r) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ (h k : ℝ), |h| ≤ M → |k| ≤ M →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((n+1:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I →
      let good := sourcePosteriorOrderedRegularity
        (N := n+1) (P := μ.maxDegree) K
      MeasurableSet good ∧
      (mixedConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu
        (WithLp.toLp 2 ![h,k])).real goodᶜ ≤
        (Fintype.card (Degree μ.maxDegree):ℝ) *
          Real.exp (-((n+1:ℕ):ℝ)/2) ∧
      ∀ J ∈ good,
        (latitudeNormalization n).toReal *
          ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
            Real.exp (-(β*C+2/(1-r^2)^2)/2) *
            (1-Q)^((((n-2:ℕ):ℝ))/2) *
            partitionAgainst
              (latitudeLaw u (latitudeFrameAt u) (Real.sqrt Q)) β
              (field (mixtureCoefficients μ) J)) ≤
          partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u I) := by
  obtain ⟨K, C, hK, hC, hgood⟩ :=
    source_mixed_conditioned_latitude_regular μ hQ hnp hM hr0 hr1
  refine ⟨K,C,hK,hC,?_⟩
  intro n hn u hu h k hh hk hband
  have hsource := hgood n (by omega) u hu h k hh hk
  dsimp only at hsource ⊢
  refine ⟨hsource.1,hsource.2.1,?_⟩
  intro J hJ
  exact sourceBand_lower_of_latitudeRegularity n hn μ u hu J I
    hQ hr0 hr1 hβ hC.le hI hband (hsource.2.2 J hJ)

/-- The same exact full-field transfer for the compatible pure-mark
value-only conditional law. -/
theorem valueConditioned_sourceBand_lower
    (μ : FiniteMixture) {Q M r β : ℝ} (hQ : 0 < Q)
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β)
    (I : Set ℝ) (hI : I ⊆ Icc (-r) r) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ h : ℝ, |h| ≤ M →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((n+1:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I →
      let good := sourcePosteriorOrderedRegularity
        (N := n+1) (P := μ.maxDegree) K
      MeasurableSet good ∧
      (valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu h).real goodᶜ ≤
        (Fintype.card (Degree μ.maxDegree):ℝ) *
          Real.exp (-((n+1:ℕ):ℝ)/2) ∧
      ∀ J ∈ good,
        (latitudeNormalization n).toReal *
          ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
            Real.exp (-(β*C+2/(1-r^2)^2)/2) *
            (1-Q)^((((n-2:ℕ):ℝ))/2) *
            partitionAgainst
              (latitudeLaw u (latitudeFrameAt u) (Real.sqrt Q)) β
              (field (mixtureCoefficients μ) J)) ≤
          partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u I) := by
  obtain ⟨K, C, hK, hC, hgood⟩ :=
    source_value_conditioned_latitude_regular μ hQ hM hr0 hr1
  refine ⟨K,C,hK,hC,?_⟩
  intro n hn u hu h hh hband
  have hsource := hgood n (by omega) u hu h hh
  dsimp only at hsource ⊢
  refine ⟨hsource.1,hsource.2.1,?_⟩
  intro J hJ
  exact sourceBand_lower_of_latitudeRegularity n hn μ u hu J I
    hQ hr0 hr1 hβ hC.le hI hband (hsource.2.2 J hJ)

/-- Under the genuine mixed full-field conditioning, the event that the
physical band falls below its literal central-section lower bound has
exponentially small probability, uniformly in bounded marks. -/
theorem mixedConditioned_sourceBand_failure
    (μ : FiniteMixture) {Q M r β : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β)
    (I : Set ℝ) (hI : I ⊆ Icc (-r) r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ (h k : ℝ), |h| ≤ M → |k| ≤ M →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((n+1:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I →
      (mixedConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu
        (WithLp.toLp 2 ![h,k])).real
        {J | partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u I) <
          (latitudeNormalization n).toReal *
            ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
              Real.exp (-(β*C+2/(1-r^2)^2)/2) *
              (1-Q)^((((n-2:ℕ):ℝ))/2) *
              partitionAgainst
                (latitudeLaw u (latitudeFrameAt u) (Real.sqrt Q)) β
                (field (mixtureCoefficients μ) J))} ≤
        (Fintype.card (Degree μ.maxDegree):ℝ) *
          Real.exp (-((n+1:ℕ):ℝ)/2) := by
  obtain ⟨K,C,hK,hC,hgood⟩ := mixedConditioned_sourceBand_lower μ hQ hnp hM
    hr0 hr1 hβ I hI
  refine ⟨C,hC,?_⟩
  intro n hn u hu h k hh hk hband
  let : IsProbabilityMeasure
      (mixedConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu
        (WithLp.toLp 2 ![h,k])) := by
    unfold mixedConditionedLaw
    infer_instance
  obtain ⟨_, htail, hbound⟩ := hgood n hn u hu h k hh hk hband
  have hsub :
      {J : Disorder (n+1) μ.maxDegree |
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u I) <
          (latitudeNormalization n).toReal *
            ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
              Real.exp (-(β*C+2/(1-r^2)^2)/2) *
              (1-Q)^((((n-2:ℕ):ℝ))/2) *
              partitionAgainst
                (latitudeLaw u (latitudeFrameAt u) (Real.sqrt Q)) β
                (field (mixtureCoefficients μ) J))} ⊆
      (sourcePosteriorOrderedRegularity
        (N := n+1) (P := μ.maxDegree) K)ᶜ := by
    intro J hbad hJ
    exact not_lt_of_ge (hbound J hJ) hbad
  exact (measureReal_mono hsub).trans htail

/-- The corresponding literal band-lower failure event under the
compatible value-only full-field conditioning. -/
theorem valueConditioned_sourceBand_failure
    (μ : FiniteMixture) {Q M r β : ℝ} (hQ : 0 < Q)
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β)
    (I : Set ℝ) (hI : I ⊆ Icc (-r) r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ h : ℝ, |h| ≤ M →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((n+1:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((n+1:ℕ):ℝ))) ⊆ I →
      (valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu h).real
        {J | partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u I) <
          (latitudeNormalization n).toReal *
            ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
              Real.exp (-(β*C+2/(1-r^2)^2)/2) *
              (1-Q)^((((n-2:ℕ):ℝ))/2) *
              partitionAgainst
                (latitudeLaw u (latitudeFrameAt u) (Real.sqrt Q)) β
                (field (mixtureCoefficients μ) J))} ≤
        (Fintype.card (Degree μ.maxDegree):ℝ) *
          Real.exp (-((n+1:ℕ):ℝ)/2) := by
  obtain ⟨K,C,hK,hC,hgood⟩ := valueConditioned_sourceBand_lower μ hQ hM
    hr0 hr1 hβ I hI
  refine ⟨C,hC,?_⟩
  intro n hn u hu h hh hband
  let : IsProbabilityMeasure
      (valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu h) := by
    unfold valueConditionedLaw
    infer_instance
  obtain ⟨_, htail, hbound⟩ := hgood n hn u hu h hh hband
  have hsub :
      {J : Disorder (n+1) μ.maxDegree |
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u I) <
          (latitudeNormalization n).toReal *
            ((2/Real.sqrt (((n+1:ℕ):ℝ))) *
              Real.exp (-(β*C+2/(1-r^2)^2)/2) *
              (1-Q)^((((n-2:ℕ):ℝ))/2) *
              partitionAgainst
                (latitudeLaw u (latitudeFrameAt u) (Real.sqrt Q)) β
                (field (mixtureCoefficients μ) J))} ⊆
      (sourcePosteriorOrderedRegularity
        (N := n+1) (P := μ.maxDegree) K)ᶜ := by
    intro J hbad hJ
    exact not_lt_of_ge (hbound J hJ) hbad
  exact (measureReal_mono hsub).trans htail

end
end SlowEquilibration.SphericalTAPPosteriorBandLower
