module

public import SphericalAging.WeightedDriftSums

public section

/-!
# Actual quadratic Itô integral representation

The martingale term below is the constructed full-filtration vector Itô
operator. The identity follows from proved quadratic variation, proved
weighted-left-sum identification, signed drift integration, and uniqueness
of limits in measure. Boundedness is an explicit local hypothesis; this
module does not infer an exit-time argument from it.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.RadialItoRepresentation
open HardSphereDynamics VectorIto VectorItoFormula VectorQuadraticVariation
  WeightedItoSums WeightedDriftSums
set_option maxHeartbeats 1200000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem quadratic_ito_formula_ae (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (X μ : ℝ≥0 → Ω → ℝ)
    (hX : ∀ s, AEStronglyMeasurable (X s) P)
    (hμ : Measurable (Function.uncurry μ))
    (hμint : ∀ t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (hdecomp : ∀ s, X s =ᵐ[P] fun ω => X 0 ω + integratedDrift μ s ω + vectorProcess D U s ω)
    (t : ℝ≥0) : TendstoInMeasure P (fun n => quadraticLeftSum X t (n + 1)) atTop
      (fun ω => X t ω ^ 2 - X 0 ω ^ 2 -
        ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω) := by
  have hA : HasQuadraticVariationInProbabilityAt (integratedDrift μ) P t (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (stronglyMeasurable_quadraticVariationApprox_integratedDrift hμ t (n+1)).aestronglyMeasurable
    · filter_upwards [hμint t] with ω hω
      exact tendsto_quadraticVariationApprox_integratedDrift_zero μ t ω
        ((integrableOn_nonnegative_iff_real (fun s => μ s ω) t).mp hω)
  have hM := vectorProcess_quadraticVariation D U t
  have hAM := hA.add_of_left_zero_of_aestronglyMeasurable hM
    (fun s => (StochasticCalculus.stronglyMeasurable_integratedDrift hμ s).aestronglyMeasurable)
    (fun s => (vectorProcess_memLp_two D U s).aestronglyMeasurable)
  have hconstant := hAM.add_timeConstant (X 0)
  have hQ : HasQuadraticVariationInProbabilityAt X P t
      (fun ω => ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω) := by
    apply hconstant.congr
    · intro s
      simpa only [add_assoc] using (hdecomp s).symm
    · exact EventuallyEq.rfl
  have hc : TendstoInMeasure P (fun _ : ℕ => fun ω => X t ω ^ 2 - X 0 ω ^ 2) atTop
      (fun ω => X t ω ^ 2 - X 0 ω ^ 2) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      convert ((hX t).pow 2).sub ((hX 0).pow 2) using 1
    · exact .of_forall (fun _ => tendsto_const_nhds)
  apply (hc.sub_real_noMeas hQ).congr
  · intro n
    exact .of_forall (fun ω => (quadraticLeftSum_identity X t (Nat.zero_lt_succ n) ω).symm)
  · exact EventuallyEq.rfl

omit [IsProbabilityMeasure P] in
lemma weightedLeftSum_decomp {X A M : ℝ≥0 → Ω → ℝ}
    (hdecomp : ∀ s, X s =ᵐ[P] fun ω => X 0 ω + A s ω + M s ω)
    (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) :
    weightedLeftSum H X T n =ᵐ[P]
      fun ω => weightedLeftSum H A T n ω + weightedLeftSum H M T n ω := by
  have h := weightedLeftSum_congr hdecomp H T n
  filter_upwards [h] with ω hω
  rw [hω]
  unfold weightedLeftSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

@[expose] def twiceState (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun s ω => 2 * X s ω

lemma stronglyAdapted_twiceState {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted 𝓕 X) :
    StronglyAdapted 𝓕 (twiceState X) := fun s => stronglyMeasurable_const.mul (hX s)

omit [IsProbabilityMeasure P] in
lemma continuous_twiceState {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ᵐ ω ∂P, Continuous (fun s => X s ω)) :
    ∀ᵐ ω ∂P, Continuous (fun s => twiceState X s ω) := by
  filter_upwards [hX] with ω hω
  exact continuous_const.mul hω

omit [MeasurableSpace Ω] in
lemma bound_twiceState {X : ℝ≥0 → Ω → ℝ} {K : ℝ≥0}
    (hK : ∀ s ω, ‖X s ω‖ ≤ K) : ∀ s ω, ‖twiceState X s ω‖ ≤ (2 * K : ℝ≥0) := by
  intro s ω
  change ‖2 * X s ω‖ ≤ ((2 * K : ℝ≥0) : ℝ)
  rw [norm_mul]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    NNReal.coe_mul, NNReal.coe_ofNat]
  exact mul_le_mul_of_nonneg_left (hK s ω) (by norm_num)

@[expose] def quadraticNoise (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (X : ℝ≥0 → Ω → ℝ)
    (hX : StronglyAdapted 𝓕 X) (hcts : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (K : ℝ≥0) (hK : ∀ s ω, ‖X s ω‖ ≤ K) (t : ℝ≥0) : RandomL2 P :=
  vectorIto D (fun i => weightedIntegrand (twiceState X) (stronglyAdapted_twiceState hX)
    (continuous_twiceState hcts) (2 * K) (bound_twiceState hK) t (U i))

/-- Actual quadratic Itô formula, with AE pathwise drift integrability
and the genuine constructed Brownian integral as its stochastic term. -/
theorem quadratic_ito_representation (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (X μ : ℝ≥0 → Ω → ℝ)
    (hX : StronglyAdapted 𝓕 X) (hcts : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (K : ℝ≥0) (hK : ∀ s ω, ‖X s ω‖ ≤ K)
    (hμ : Measurable (Function.uncurry μ))
    (hμint : ∀ t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (hdecomp : ∀ s, X s =ᵐ[P] fun ω => X 0 ω + integratedDrift μ s ω + vectorProcess D U s ω)
    (t : ℝ≥0) : ∀ᵐ ω ∂P, X t ω ^ 2 = X 0 ω ^ 2 +
      (∫ s in Ioc 0 t, 2 * X s ω * μ s ω ∂nonnegativeLebesgueMeasure) +
      (quadraticNoise D U X hX hcts K hK t : Ω → ℝ) ω +
      ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω := by
  have hQ := quadratic_ito_formula_ae D U X μ
    (fun s => ((hX s).mono (𝓕.le s)).aestronglyMeasurable) hμ hμint hdecomp t
  have hDrift := adapted_weightedDrift_tendsto (twiceState X) μ (stronglyAdapted_twiceState hX)
    (continuous_twiceState hcts) (2 * K) (bound_twiceState hK) t hμ (hμint t)
  have hNoise := vector_weightedLeftSum_tendsto D (twiceState X) (stronglyAdapted_twiceState hX)
    (continuous_twiceState hcts) (2 * K) (bound_twiceState hK) t U
  have hTotal := hDrift.add_real_noMeas hNoise
  have hTotal' : TendstoInMeasure P (fun n => quadraticLeftSum X t (n+1)) atTop
      (fun ω => (∫ s in Ioc 0 t, 2 * X s ω * μ s ω ∂nonnegativeLebesgueMeasure) +
        (quadraticNoise D U X hX hcts K hK t : Ω → ℝ) ω) := by
    apply hTotal.congr
    · intro n
      exact (weightedLeftSum_decomp hdecomp (twiceState X) t (n+1)).symm
    · exact EventuallyEq.rfl
  have heq := tendstoInMeasure_ae_unique hQ hTotal'
  filter_upwards [heq] with ω hω
  linarith

/-- Matrix-noise norm formula obtained by summing the actual scalar
identities. The correction term is the full matrix trace, including all
independent driving coordinates. -/
theorem quadratic_norm_ito_representation {L : ℕ} (D : BrownianDriver N P 𝓕)
    (U : Fin L → Fin N → PredictableProcessL2 𝓕 P) (X μ : Fin L → ℝ≥0 → Ω → ℝ)
    (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hcts : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K)
    (hμ : ∀ k, Measurable (Function.uncurry (μ k)))
    (hμint : ∀ k t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ k s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (hdecomp : ∀ k s, X k s =ᵐ[P] fun ω =>
      X k 0 ω + integratedDrift (μ k) s ω + vectorProcess D (U k) s ω)
    (t : ℝ≥0) : ∀ᵐ ω ∂P,
      (∑ k, X k t ω ^ 2) = (∑ k, X k 0 ω ^ 2) +
        (∑ k, ∫ s in Ioc 0 t, 2 * X k s ω * μ k s ω ∂nonnegativeLebesgueMeasure) +
        (∑ k, (quadraticNoise D (U k) (X k) (hX k) (hcts k) K (hK k) t : Ω → ℝ) ω) +
        ∑ k, ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U k i) t ω := by
  have hall := ae_all_iff.mpr (fun k : Fin L => quadratic_ito_representation D (U k) (X k) (μ k)
    (hX k) (hcts k) K (hK k) (hμ k) (hμint k) (hdecomp k) t)
  filter_upwards [hall] with ω hω
  calc
    (∑ k, X k t ω ^ 2) = ∑ k, (X k 0 ω ^ 2 +
      (∫ s in Ioc 0 t, 2 * X k s ω * μ k s ω ∂nonnegativeLebesgueMeasure) +
      (quadraticNoise D (U k) (X k) (hX k) (hcts k) K (hK k) t : Ω → ℝ) ω +
      ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U k i) t ω) :=
      Finset.sum_congr rfl (fun k _ => hω k)
    _ = _ := by simp only [Finset.sum_add_distrib]

end SphericalAging.RadialItoRepresentation
