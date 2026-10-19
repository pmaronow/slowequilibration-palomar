module

public import SphericalAging.LocalWeightedQuadratic

public section

/-! Genuine first-order weighted partition sums for an actual strong SDE
coordinate, retaining its true predictable stochastic integrand. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.SDEWeightedLinear
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open VectorIto WeightedItoSums WeightedDriftSums LocalRadialIto AnnealedSDECore
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The actual finite-variation drift version has the genuine weighted
left sum limit, derived from its predictable representative. -/
theorem driftVersion_weightedLeftSum_tendsto (A : PredictableProcessL2 F P)
    (T t : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted F H)
    (hHc : ∀ᵐ ω ∂P,Continuous (fun s => H s ω)) (K : ℝ≥0)
    (hK : ∀ s ω,‖H s ω‖≤K) :
    TendstoInMeasure P (fun n => weightedLeftSum H (driftVersion A T) t (n+1)) atTop
      (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*cutRepresentative A T (s,ω) ∂nonnegativeLebesgueMeasure) := by
  let μ : ℝ≥0 → Ω → ℝ := fun s ω => cutRepresentative A T (s,ω)
  have hμ : Measurable (Function.uncurry μ) :=
    (cutRepresentative_stronglyMeasurable A T).mono (predictable_le_prod F) |>.measurable
  have he : driftVersion A T=integratedDrift μ := by
    funext s ω
    exact driftPrimitive_eq_integratedDrift μ s ω
  rw [he]
  exact adapted_weightedDrift_tendsto H μ hH hHc K hK t hμ
    ((cutRepresentative_integrable A T).prod_left_ae.mono (fun _ hi => hi.integrableOn))

/-- Prefix form of the true weighted first-order SDE increment limit. -/
theorem prefix_weightedLeftSum_tendsto (D : BrownianDriver N P F)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P)
    (T t : ℝ≥0) (ht : t≤T) (W H : ℝ≥0 → Ω → ℝ) (z0 : Ω → ℝ)
    (hprefix : ∀ s,s≤T → W s=ᵐ[P]
      fun ω => z0 ω+driftVersion A T s ω+vectorProcess D U s ω)
    (hH : StronglyAdapted F H) (hHc : ∀ᵐ ω ∂P,Continuous (fun s => H s ω))
    (K : ℝ≥0) (hK : ∀ s ω,‖H s ω‖≤K) :
    TendstoInMeasure P (fun n => weightedLeftSum H W t (n+1)) atTop
      (fun ω => (∫ s in Ioc (0 : ℝ≥0) t,H s ω*cutRepresentative A T (s,ω) ∂nonnegativeLebesgueMeasure)+
        (vectorIto D (fun j => weightedIntegrand H hH hHc K hK t (U j)) : Ω → ℝ) ω) := by
  have hd := driftVersion_weightedLeftSum_tendsto A T t H hH hHc K hK
  have hi := vector_weightedLeftSum_tendsto D H hH hHc K hK t U
  apply (hd.add_real_noMeas hi).congr_left
  intro n
  have he := weightedLeftSum_congr_on H t (fun s hs => hprefix s (hs.trans ht))
    (n+1) (Nat.zero_lt_succ n)
  filter_upwards [he] with ω hω
  rw [hω]
  unfold weightedLeftSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun l _ => by ring)

/-- True predictable drift identification converts the weighted drift
limit to the displayed physical coefficient evaluation. -/
lemma weighted_drift_eq_actual (A : PredictableProcessL2 F P) (T t : ℝ≥0) (ht : t≤T)
    (H μ : ℝ≥0 → Ω → ℝ)
    (hA : (A : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut μ T) :
    (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*cutRepresentative A T (s,ω) ∂nonnegativeLebesgueMeasure)=ᵐ[P]
      fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*μ s ω ∂nonnegativeLebesgueMeasure := by
  have hrep : cutRepresentative A T=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut μ T := by
    filter_upwards [representative_ae A,hA] with q hr ha
    simp only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      Set.indicator,Set.mem_prod,Set.mem_univ,and_true,FourPapersCommon.continuousAdaptedTimeCut,hr,ha]
    split <;> rfl
  have hswap := (Measure.measurePreserving_swap (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp hrep
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hω,ae_restrict_mem measurableSet_Ioc] with s hs hst
  dsimp only [Function.comp_def,Prod.swap] at hs
  rw [hs]
  simp only [FourPapersCommon.continuousAdaptedTimeCut,
    ite_eq_left (show s ∈ Ioc (0 : ℝ≥0) T from ⟨hst.1,hst.2.trans ht⟩)]

end SphericalAging.SDEWeightedLinear
