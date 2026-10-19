module

public import SphericalAging.StoppedSDE

public section

/-! Predictable classes of the actual radial drift and radial noise.
These are assembled from the genuine matrix Itô coefficients. No radial
equation or sphere preservation is a field of the data.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.RadialProcess
open HardSphereDynamics VectorIto WeightedItoSums RadialItoRepresentation
set_option maxHeartbeats 1600000
variable {N L : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma weightedIntegrand_timeRestrict (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun s => H s ω)) (K : ℝ≥0) (hK : ∀ s ω, ‖H s ω‖ ≤ K)
    (T t : ℝ≥0) (ht : t ≤ T) (U : PredictableProcessL2 𝓕 P) :
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 t
      (weightedIntegrand H hH hc K hK T U) = weightedIntegrand H hH hc K hK t U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn 𝓕 t
      (weightedIntegrand H hH hc K hK T U),
    predictableProduct_coe (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut 𝓕 H hH hc T)
      K (.of_forall (timeCut_bound H K hK T)) U,
    predictableProduct_coe (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut 𝓕 H hH hc t)
      K (.of_forall (timeCut_bound H K hK t)) U] with p hcut hT ht'
  rw [hcut]
  unfold FourPapersCommon.FilteredBrownian.predictableTimeFrame
  by_cases hp : p.1 ∈ Ioc (0 : ℝ≥0) t
  · rw [indicator_of_mem (show p ∈ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) from ⟨hp, mem_univ _⟩)]
    change (predictableProduct _ K _ U : ℝ≥0 × Ω → ℝ) p = _
    rw [hT]
    have hpT : p.1 ∈ Ioc (0 : ℝ≥0) T := ⟨hp.1, hp.2.trans ht⟩
    change _ = (predictableProduct _ K _ U : ℝ≥0 × Ω → ℝ) p
    rw [ht']
    simp only [FourPapersCommon.continuousAdaptedTimeCut, hp, hpT, ite_true]
  · rw [indicator_of_notMem (show p ∉ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) from fun h => hp h.1)]
    change _ = (predictableProduct _ K _ U : ℝ≥0 × Ω → ℝ) p
    rw [ht']
    simp only [FourPapersCommon.continuousAdaptedTimeCut, hp, ite_false, zero_mul]

@[expose] def radialNoise (U : Fin L → Fin N → PredictableProcessL2 𝓕 P)
    (X : Fin L → ℝ≥0 → Ω → ℝ) (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hc : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K) (T : ℝ≥0) (i : Fin N) :
    PredictableProcessL2 𝓕 P := ∑ k, weightedIntegrand (twiceState (X k))
      (stronglyAdapted_twiceState (hX k)) (continuous_twiceState (hc k)) (2 * K) (bound_twiceState (hK k)) T (U k i)

theorem sum_quadraticNoise (D : BrownianDriver N P 𝓕)
    (U : Fin L → Fin N → PredictableProcessL2 𝓕 P)
    (X : Fin L → ℝ≥0 → Ω → ℝ) (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hc : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K) (T t : ℝ≥0) (ht : t ≤ T) :
    (∑ k, quadraticNoise D (U k) (X k) (hX k) (hc k) K (hK k) t) =
      vectorProcessLp D (radialNoise U X hX hc K hK T) t := by
  unfold quadraticNoise vectorProcessLp radialNoise vectorIto
  change (∑ k, ∑ i, coordinateIto D i (weightedIntegrand _ _ _ _ _ t (U k i))) =
    ∑ i, coordinateIto D i ((FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM 𝓕 t)
      (∑ k, weightedIntegrand _ _ _ _ _ T (U k i)))
  simp only [map_sum, FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [weightedIntegrand_timeRestrict _ _ _ _ _ T t ht]

@[expose] def predictableSquare (U : PredictableProcessL2 𝓕 P) (K : ℝ≥0)
    (hK : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖(U : ℝ≥0 × Ω → ℝ) p‖ ≤ K) :
    PredictableProcessL2 𝓕 P := predictableProduct (lpMeas.aestronglyMeasurable U) K hK U

omit [IsProbabilityMeasure P] in
lemma predictableSquare_coe (U : PredictableProcessL2 𝓕 P) (K : ℝ≥0)
    (hK : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖(U : ℝ≥0 × Ω → ℝ) p‖ ≤ K) :
    (predictableSquare U K hK : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => (U : ℝ≥0 × Ω → ℝ) p ^ 2 := by
  simpa only [predictableSquare, pow_two] using predictableProduct_coe
    (lpMeas.aestronglyMeasurable U) K hK U

@[expose] def radialDrift (A : Fin L → PredictableProcessL2 𝓕 P)
    (U : Fin L → Fin N → PredictableProcessL2 𝓕 P)
    (X : Fin L → ℝ≥0 → Ω → ℝ) (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hc : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K) (S : ℝ≥0)
    (hS : ∀ k i, ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖(U k i : ℝ≥0 × Ω → ℝ) p‖ ≤ S)
    (T : ℝ≥0) : PredictableProcessL2 𝓕 P :=
  (∑ k, weightedIntegrand (twiceState (X k)) (stronglyAdapted_twiceState (hX k))
    (continuous_twiceState (hc k)) (2 * K) (bound_twiceState (hK k)) T (A k)) +
      ∑ k, ∑ i, predictableSquare (U k i) S (hS k i)

omit [IsProbabilityMeasure P] in
lemma predictable_sum_coe {ι : Type*} [Fintype ι] (W : ι → PredictableProcessL2 𝓕 P) :
    (∑ i, W i : PredictableProcessL2 𝓕 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => ∑ i, (W i : ℝ≥0 × Ω → ℝ) p := by
  simpa only [Submodule.coe_sum] using Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => (W i : TimeProcessL2 P))

lemma weighted_sum_coe (A : Fin L → PredictableProcessL2 𝓕 P)
    (X : Fin L → ℝ≥0 → Ω → ℝ) (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hc : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K) (T : ℝ≥0) :
    (∑ k, weightedIntegrand (twiceState (X k)) (stronglyAdapted_twiceState (hX k))
      (continuous_twiceState (hc k)) (2 * K) (bound_twiceState (hK k)) T (A k) : PredictableProcessL2 𝓕 P)
      =ᵐ[nonnegativeLebesgueMeasure.prod P] fun p =>
        ∑ k, FourPapersCommon.continuousAdaptedTimeCut (twiceState (X k)) T p *
          (A k : ℝ≥0 × Ω → ℝ) p := by
  let W (k : Fin L) := weightedIntegrand (twiceState (X k)) (stronglyAdapted_twiceState (hX k))
      (continuous_twiceState (hc k)) (2 * K) (bound_twiceState (hK k)) T (A k)
  have hall : ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ∀ k,
      (W k : ℝ≥0 × Ω → ℝ) p = FourPapersCommon.continuousAdaptedTimeCut (twiceState (X k)) T p *
        (A k : ℝ≥0 × Ω → ℝ) p := ae_all_iff.mpr (fun k => predictableProduct_coe _ _ _ _)
  filter_upwards [predictable_sum_coe W, hall] with p hsum hp
  exact hsum.trans (Finset.sum_congr rfl (fun k _ => hp k))

omit [IsProbabilityMeasure P] in
lemma square_trace_coe (U : Fin L → Fin N → PredictableProcessL2 𝓕 P) (S : ℝ≥0)
    (hS : ∀ k i, ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖(U k i : ℝ≥0 × Ω → ℝ) p‖ ≤ S) :
    (∑ k, ∑ i, predictableSquare (U k i) S (hS k i) : PredictableProcessL2 𝓕 P)
      =ᵐ[nonnegativeLebesgueMeasure.prod P] fun p => ∑ k, ∑ i, (U k i : ℝ≥0 × Ω → ℝ) p ^ 2 := by
  have hinner (k : Fin L) : (∑ i, predictableSquare (U k i) S (hS k i) : PredictableProcessL2 𝓕 P)
      =ᵐ[nonnegativeLebesgueMeasure.prod P] fun p => ∑ i, (U k i : ℝ≥0 × Ω → ℝ) p ^ 2 := by
    have hall := ae_all_iff.mpr (fun i : Fin N => predictableSquare_coe (U k i) S (hS k i))
    filter_upwards [predictable_sum_coe (fun i => predictableSquare (U k i) S (hS k i)), hall] with p hsum hp
    exact hsum.trans (Finset.sum_congr rfl (fun i _ => hp i))
  have hall := ae_all_iff.mpr hinner
  filter_upwards [predictable_sum_coe (fun k => ∑ i, predictableSquare (U k i) S (hS k i)), hall] with p hsum hp
  exact hsum.trans (Finset.sum_congr rfl (fun k _ => hp k))

theorem radialDrift_coe (A : Fin L → PredictableProcessL2 𝓕 P)
    (U : Fin L → Fin N → PredictableProcessL2 𝓕 P)
    (X : Fin L → ℝ≥0 → Ω → ℝ) (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hc : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K) (S : ℝ≥0)
    (hS : ∀ k i, ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖(U k i : ℝ≥0 × Ω → ℝ) p‖ ≤ S)
    (T : ℝ≥0) : (radialDrift A U X hX hc K hK S hS T : ℝ≥0 × Ω → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P] fun p =>
        (∑ k, FourPapersCommon.continuousAdaptedTimeCut (twiceState (X k)) T p *
          (A k : ℝ≥0 × Ω → ℝ) p) + ∑ k, ∑ i, (U k i : ℝ≥0 × Ω → ℝ) p ^ 2 := by
  let B : PredictableProcessL2 𝓕 P := ∑ k, weightedIntegrand (twiceState (X k))
    (stronglyAdapted_twiceState (hX k)) (continuous_twiceState (hc k)) (2 * K) (bound_twiceState (hK k)) T (A k)
  let C : PredictableProcessL2 𝓕 P := ∑ k, ∑ i, predictableSquare (U k i) S (hS k i)
  change ((B + C : PredictableProcessL2 𝓕 P) : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] _
  filter_upwards [Lp.coeFn_add (B : TimeProcessL2 P) (C : TimeProcessL2 P),
    weighted_sum_coe A X hX hc K hK T, square_trace_coe U S hS] with p hadd hb hc'
  change (((B : TimeProcessL2 P) + (C : TimeProcessL2 P) : TimeProcessL2 P) : ℝ≥0 × Ω → ℝ) p = _
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hb, hc']

theorem radialNoise_coe (U : Fin L → Fin N → PredictableProcessL2 𝓕 P)
    (X : Fin L → ℝ≥0 → Ω → ℝ) (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hc : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K) (T : ℝ≥0) (i : Fin N) :
    (radialNoise U X hX hc K hK T i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => ∑ k, FourPapersCommon.continuousAdaptedTimeCut (twiceState (X k)) T p *
        (U k i : ℝ≥0 × Ω → ℝ) p := weighted_sum_coe (fun k => U k i) X hX hc K hK T

theorem driftVersion_eq_of_coe (A : PredictableProcessL2 𝓕 P) (f : ℝ≥0 × Ω → ℝ)
    (hA : (A : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] f) (t : ℝ≥0) :
    PredictableDriftTime.driftVersion A t t =ᵐ[P]
      fun ω => ∫ s in Ioc 0 t, f (s, ω) ∂nonnegativeLebesgueMeasure := by
  have hrep := (PredictableDriftTime.representative_ae A).trans hA
  have hs := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp hrep)
  filter_upwards [hs] with ω hω
  unfold PredictableDriftTime.driftVersion PredictableDriftTime.primitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hω, ae_restrict_mem measurableSet_Ioc] with s hs hst
  have hs' : PredictableDriftTime.representative A (s, ω) = f (s, ω) := by
    simpa only [Function.comp_apply, Prod.swap_prod_mk] using hs
  simp only [PredictableDriftTime.cutRepresentative,
    FourPapersCommon.FilteredBrownian.predictableTimeFrame,
    indicator_of_mem (show (s, ω) ∈ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) from ⟨hst, mem_univ _⟩), hs']

theorem radialDrift_version (A : Fin L → PredictableProcessL2 𝓕 P)
    (U : Fin L → Fin N → PredictableProcessL2 𝓕 P)
    (X μ : Fin L → ℝ≥0 → Ω → ℝ) (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hc : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K) (S : ℝ≥0)
    (hS : ∀ k i, ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖(U k i : ℝ≥0 × Ω → ℝ) p‖ ≤ S)
    (T t : ℝ≥0) (ht : t ≤ T)
    (hA : ∀ k, (A k : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] fun p => μ k p.1 p.2)
    (hμint : ∀ k, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ k s ω) (Ioc 0 t) nonnegativeLebesgueMeasure) :
    PredictableDriftTime.driftVersion (radialDrift A U X hX hc K hK S hS T) t t =ᵐ[P]
      fun ω => (∑ k, ∫ s in Ioc 0 t, 2 * X k s ω * μ k s ω ∂nonnegativeLebesgueMeasure) +
        ∑ k, ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U k i) t ω := by
  have hv := driftVersion_eq_of_coe _ _ (radialDrift_coe A U X hX hc K hK S hS T) t
  have hAs : ∀ᵐ ω ∂P, ∀ k, ∀ᵐ s ∂nonnegativeLebesgueMeasure,
      (A k : ℝ≥0 × Ω → ℝ) (s, ω) = μ k s ω := by
    apply ae_all_iff.mpr
    intro k
    exact Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp (hA k))
  have hCs := ae_all_iff.mpr hc
  have hInts := ae_all_iff.mpr hμint
  have hUs : ∀ᵐ ω ∂P, ∀ k i,
      Integrable (fun s => (U k i : ℝ≥0 × Ω → ℝ) (s, ω)^2) nonnegativeLebesgueMeasure :=
    ae_all_iff.mpr (fun k => ae_all_iff.mpr (fun i => (Lp.memLp (U k i : TimeProcessL2 P)).integrable_sq.prod_left_ae))
  filter_upwards [hv, hAs, hCs, hInts, hUs] with ω hv hA hc hi hU
  rw [hv]
  have hw (k : Fin L) : IntegrableOn (fun s => 2 * X k s ω * μ k s ω)
      (Ioc 0 t) nonnegativeLebesgueMeasure :=
    (hi k).bdd_mul (continuous_const.mul (hc k)).aestronglyMeasurable
      (.of_forall (fun s => bound_twiceState (hK k) s ω))
  have hlin : IntegrableOn (fun s => ∑ k, 2 * X k s ω * μ k s ω) (Ioc 0 t) nonnegativeLebesgueMeasure :=
    integrable_finsetSum Finset.univ (fun k _ => hw k)
  have hsquare (k : Fin L) : IntegrableOn (fun s => ∑ i, (U k i : ℝ≥0 × Ω → ℝ) (s, ω)^2)
      (Ioc 0 t) nonnegativeLebesgueMeasure :=
    integrable_finsetSum Finset.univ (fun i _ => (hU k i).integrableOn)
  have htrace : IntegrableOn (fun s => ∑ k, ∑ i, (U k i : ℝ≥0 × Ω → ℝ) (s, ω)^2)
      (Ioc 0 t) nonnegativeLebesgueMeasure := integrable_finsetSum Finset.univ (fun k _ => hsquare k)
  have heq : (∫ s in Ioc 0 t,
      (∑ k, FourPapersCommon.continuousAdaptedTimeCut (twiceState (X k)) T (s, ω) *
        (A k : ℝ≥0 × Ω → ℝ) (s, ω)) + ∑ k, ∑ i, (U k i : ℝ≥0 × Ω → ℝ) (s, ω)^2
      ∂nonnegativeLebesgueMeasure) =
        ∫ s in Ioc 0 t, (∑ k, 2 * X k s ω * μ k s ω) + ∑ k, ∑ i, (U k i : ℝ≥0 × Ω → ℝ) (s, ω)^2
          ∂nonnegativeLebesgueMeasure := by
    apply integral_congr_ae
    have hall := ae_all_iff.mpr hA
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioc] with s hs hst
    have hsT : s ∈ Ioc (0 : ℝ≥0) T := ⟨hst.1, hst.2.trans ht⟩
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [FourPapersCommon.continuousAdaptedTimeCut, hsT, ite_true, twiceState]
    rw [hs k]
  rw [heq, integral_add hlin htrace, integral_finsetSum Finset.univ (fun k _ => hw k),
    integral_finsetSum Finset.univ (fun k _ => hsquare k)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact integral_finsetSum Finset.univ (fun i _ => (hU k i).integrableOn)

/-- The actual matrix SDE yields an actual predictable radial SDE.
Both radial classes are explicitly assembled above; their equation is a
theorem, not a premise of the data. -/
theorem quadratic_class_equation (D : BrownianDriver N P 𝓕)
    (A : Fin L → PredictableProcessL2 𝓕 P)
    (U : Fin L → Fin N → PredictableProcessL2 𝓕 P)
    (X μ : Fin L → ℝ≥0 → Ω → ℝ) (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hc : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K) (S : ℝ≥0)
    (hS : ∀ k i, ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖(U k i : ℝ≥0 × Ω → ℝ) p‖ ≤ S)
    (T t : ℝ≥0) (ht : t ≤ T)
    (hA : ∀ k, (A k : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] fun p => μ k p.1 p.2)
    (hμ : ∀ k, Measurable (Function.uncurry (μ k)))
    (hμint : ∀ k s, ∀ᵐ ω ∂P, IntegrableOn (fun r => μ k r ω) (Ioc 0 s) nonnegativeLebesgueMeasure)
    (hdecomp : ∀ k s, X k s =ᵐ[P] fun ω => X k 0 ω + integratedDrift (μ k) s ω + vectorProcess D (U k) s ω) :
    (fun ω => (∑ k, X k t ω ^ 2) - ∑ k, X k 0 ω ^ 2) =ᵐ[P]
      fun ω => PredictableDriftTime.driftVersion (radialDrift A U X hX hc K hK S hS T) t t ω +
        (vectorProcessLp D (radialNoise U X hX hc K hK T) t : Ω → ℝ) ω := by
  have hn := quadratic_norm_ito_representation D U X μ hX hc K hK hμ hμint hdecomp t
  have hd := radialDrift_version A U X μ hX hc K hK S hS T t ht hA (fun k => hμint k t)
  have heq := Lp.coeFn_fun_finsetSum Finset.univ
    (fun k => quadraticNoise D (U k) (X k) (hX k) (hc k) K (hK k) t)
  rw [sum_quadraticNoise D U X hX hc K hK T t ht] at heq
  filter_upwards [hn, hd, heq] with ω hn hd heq
  linarith

theorem zero_initial_radius_class_equation (D : BrownianDriver N P 𝓕)
    (A : Fin L → PredictableProcessL2 𝓕 P)
    (U : Fin L → Fin N → PredictableProcessL2 𝓕 P)
    (X μ : Fin L → ℝ≥0 → Ω → ℝ) (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hc : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K) (S : ℝ≥0)
    (hS : ∀ k i, ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖(U k i : ℝ≥0 × Ω → ℝ) p‖ ≤ S)
    (T t : ℝ≥0) (ht : t ≤ T) (r0 : ℝ) (hinitial : ∀ᵐ ω ∂P, (∑ k, X k 0 ω ^ 2) = r0)
    (hA : ∀ k, (A k : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] fun p => μ k p.1 p.2)
    (hμ : ∀ k, Measurable (Function.uncurry (μ k)))
    (hμint : ∀ k s, ∀ᵐ ω ∂P, IntegrableOn (fun r => μ k r ω) (Ioc 0 s) nonnegativeLebesgueMeasure)
    (hdecomp : ∀ k s, X k s =ᵐ[P] fun ω => X k 0 ω + integratedDrift (μ k) s ω + vectorProcess D (U k) s ω) :
    (fun ω => (∑ k, X k t ω ^ 2) - r0) =ᵐ[P]
      fun ω => PredictableDriftTime.driftVersion (radialDrift A U X hX hc K hK S hS T) t t ω +
        (vectorProcessLp D (radialNoise U X hX hc K hK T) t : Ω → ℝ) ω := by
  have h := quadratic_class_equation D A U X μ hX hc K hK S hS T t ht hA hμ hμint hdecomp
  filter_upwards [h, hinitial] with ω hω h0
  simpa only [h0] using hω

end SphericalAging.RadialProcess
