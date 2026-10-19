module

public import SphericalAging.VectorQuadraticVariation
public import StochasticCalculus.WeightedBracketRiemann

public section

/-!
# Itô's formula for the constructed Brownian vector in its full filtration

The predictable diffusion is the actual finite family of integrands, and
its bracket is proved from the realized independent Brownian drivers.
The formula characterizes the space integral by its left partition sums.
This is the same partition characterization as the vendor's verified Itô
formula. Identifying that space integral with a separately constructed
weighted Brownian integral is a further representation theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.VectorItoFormula
open HardSphereDynamics VectorIto VectorQuadraticVariation
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def diffusionMagnitude (U : Fin N → PredictableProcessL2 𝓕 P) (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.sqrt (∑ i, ((U i : ℝ≥0 × Ω → ℝ) (s, ω)) ^ 2)

omit [IsProbabilityMeasure P] in
lemma diffusionMagnitude_sq (U : Fin N → PredictableProcessL2 𝓕 P) (s : ℝ≥0) (ω : Ω) :
    diffusionMagnitude U s ω ^ 2 = ∑ i, ((U i : ℝ≥0 × Ω → ℝ) (s, ω)) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma diffusionMagnitude_integrable_sq (U : Fin N → PredictableProcessL2 𝓕 P)
    (t : ℝ≥0) : ∀ᵐ ω ∂P, IntegrableOn (fun s => diffusionMagnitude U s ω ^ 2)
      (Set.Ioc 0 t) nonnegativeLebesgueMeasure := by
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin N,
      Integrable (fun s => ((U i : ℝ≥0 × Ω → ℝ) (s, ω)) ^ 2) nonnegativeLebesgueMeasure :=
    ae_all_iff.mpr (fun i => ((Lp.memLp (U i : TimeProcessL2 P)).integrable_sq).prod_left_ae)
  filter_upwards [hall] with ω hω
  simp only [diffusionMagnitude_sq]
  exact integrable_finsetSum Finset.univ (fun i _ => (hω i).integrableOn)

lemma diffusionBracket_eq_integral (U : Fin N → PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    (fun ω => ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω) =ᵐ[P]
      fun ω => ∫ s in Set.Ioc (0 : ℝ≥0) t, diffusionMagnitude U s ω ^ 2 ∂nonnegativeLebesgueMeasure := by
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin N,
      Integrable (fun s => ((U i : ℝ≥0 × Ω → ℝ) (s, ω)) ^ 2) nonnegativeLebesgueMeasure :=
    ae_all_iff.mpr (fun i => ((Lp.memLp (U i : TimeProcessL2 P)).integrable_sq).prod_left_ae)
  filter_upwards [hall] with ω hω
  simp only [diffusionMagnitude_sq, FilteredQuadraticVariation.predictableQuadraticVariation]
  exact (integral_finsetSum Finset.univ (fun i _ => (hω i).integrableOn)).symm

lemma vectorProcess_beforeStop_diffusionMagnitude (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (t a : ℝ≥0) :
    TendstoInMeasure P (fun n => quadraticVariationBeforeStopApprox (vectorProcess D U) t (n + 1) a)
      atTop (fun ω => ∫ s in Set.Ioc (0 : ℝ≥0) (min t a), diffusionMagnitude U s ω ^ 2
        ∂nonnegativeLebesgueMeasure) :=
  (vectorProcess_beforeStop_all D U t a).congr_right (diffusionBracket_eq_integral U _)

/-- The Itô chain rule for a process driven by the actual `N`-coordinate
full-filtration stochastic integral. No bracket premise is supplied:
it is derived from the Brownian driver and the predictable diffusion. -/
theorem exists_ito_formula (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (X μ Y : ℝ≥0 → Ω → ℝ)
    (hX : ∀ s, AEStronglyMeasurable (X s) P)
    (hμ : Measurable (Function.uncurry μ))
    (hμint : ∀ t ω, IntegrableOn (fun s : ℝ => μ s.toNNReal ω) (Set.Icc 0 (t : ℝ)))
    (hmod : IsContinuousProcessModification X Y P)
    (hdecomp : ∀ s, X s =ᵐ[P] fun ω => X 0 ω + integratedDrift μ s ω + vectorProcess D U s ω)
    (f : ℝ → ℝ → ℝ) (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) :
    ∃ I : Ω → ℝ,
      TendstoInMeasure P (fun n => generalItoSpaceApprox f X t (n + 1)) atTop I ∧
      ∀ᵐ ω ∂P, f t (X t ω) = f 0 (X 0 ω) + generalItoTimeIntegral f Y t ω + I ω +
        generalItoQuadraticIntegral f Y (diffusionMagnitude U) t ω := by
  exact exists_ito_formula_of_characteristics X μ (diffusionMagnitude U) (vectorProcess D U) Y hX
    (fun s => (vectorProcess_memLp_two D U s).aestronglyMeasurable) hμ hμint hmod hdecomp
    (vectorProcess_beforeStop_diffusionMagnitude D U) (diffusionMagnitude_integrable_sq U)
    f hf htdiff hslice hdt hdx hsecond t

@[expose] def quadraticLeftSum (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, 2 * X (uniformPartitionTime t n k) ω *
    (X (uniformPartitionTime t n (k + 1)) ω - X (uniformPartitionTime t n k) ω)

omit [IsProbabilityMeasure P] [MeasurableSpace Ω] in
lemma quadraticLeftSum_identity (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    quadraticLeftSum X t n ω = X t ω ^ 2 - X 0 ω ^ 2 - quadraticVariationApprox X t n ω := by
  have hsum : quadraticLeftSum X t n ω + quadraticVariationApprox X t n ω =
      X t ω ^ 2 - X 0 ω ^ 2 := by
    unfold quadraticLeftSum quadraticVariationApprox
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ k ∈ Finset.range n,
          (X (uniformPartitionTime t n (k + 1)) ω ^ 2 - X (uniformPartitionTime t n k) ω ^ 2) :=
        Finset.sum_congr rfl (fun k _ => by ring)
      _ = _ := by
        rw [Finset.sum_range_sub (fun k => X (uniformPartitionTime t n k) ω ^ 2) n]
        have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
        simp [uniformPartitionTime, hn0]
  linarith

lemma quadraticVariation_of_vector_driven (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (X μ : ℝ≥0 → Ω → ℝ)
    (hμ : Measurable (Function.uncurry μ))
    (hμint : ∀ t ω, IntegrableOn (fun s : ℝ => μ s.toNNReal ω) (Set.Icc 0 (t : ℝ)))
    (hdecomp : ∀ s, X s =ᵐ[P] fun ω => X 0 ω + integratedDrift μ s ω + vectorProcess D U s ω)
    (t : ℝ≥0) : HasQuadraticVariationInProbabilityAt X P t
      (fun ω => ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω) := by
  have hA := quadraticVariation_integratedDrift_inProbability (P := P) hμ t (hμint t)
  have hM := vectorProcess_quadraticVariation D U t
  have hAM := hA.add_of_left_zero_of_aestronglyMeasurable hM
    (fun s => (stronglyMeasurable_integratedDrift hμ s).aestronglyMeasurable)
    (fun s => (vectorProcess_memLp_two D U s).aestronglyMeasurable)
  have hconstant := hAM.add_timeConstant (X 0)
  apply hconstant.congr
  · intro s
    simpa only [add_assoc] using (hdecomp s).symm
  · exact EventuallyEq.rfl

/-- The quadratic Itô formula for an actual matrix row of Brownian
integrands, expressed through its defining left-endpoint space sums. -/
theorem quadratic_ito_formula (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (X μ : ℝ≥0 → Ω → ℝ)
    (hX : ∀ s, AEStronglyMeasurable (X s) P)
    (hμ : Measurable (Function.uncurry μ))
    (hμint : ∀ t ω, IntegrableOn (fun s : ℝ => μ s.toNNReal ω) (Set.Icc 0 (t : ℝ)))
    (hdecomp : ∀ s, X s =ᵐ[P] fun ω => X 0 ω + integratedDrift μ s ω + vectorProcess D U s ω)
    (t : ℝ≥0) : TendstoInMeasure P (fun n => quadraticLeftSum X t (n + 1)) atTop
      (fun ω => X t ω ^ 2 - X 0 ω ^ 2 -
        ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω) := by
  have hQ := quadraticVariation_of_vector_driven D U X μ hμ hμint hdecomp t
  have hconstant : TendstoInMeasure P (fun _ : ℕ => fun ω => X t ω ^ 2 - X 0 ω ^ 2) atTop
      (fun ω => X t ω ^ 2 - X 0 ω ^ 2) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      convert ((hX t).pow 2).sub ((hX 0).pow 2) using 1
    · exact Eventually.of_forall (fun _ => tendsto_const_nhds)
  apply (hconstant.sub_real_noMeas hQ).congr
  · intro n
    exact Eventually.of_forall (fun ω =>
      (quadraticLeftSum_identity X t (Nat.zero_lt_succ n) ω).symm)
  · exact EventuallyEq.rfl

lemma tendstoInMeasure_finsetSum {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℕ → Ω → ℝ) (g : ι → Ω → ℝ)
    (h : ∀ i ∈ S, TendstoInMeasure P (f i) atTop (g i)) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ S, f i n ω) atTop (fun ω => ∑ i ∈ S, g i ω) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact aestronglyMeasurable_const
    · exact Eventually.of_forall (fun _ => tendsto_const_nhds)
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add_real_noMeas
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- For every finite state dimension and noise dimension, the quadratic
norm correction is the trace of the actual diffusion matrix bracket. -/
theorem quadratic_norm_ito_formula {K : ℕ} (D : BrownianDriver N P 𝓕)
    (U : Fin K → Fin N → PredictableProcessL2 𝓕 P)
    (X μ : Fin K → ℝ≥0 → Ω → ℝ)
    (hX : ∀ k s, AEStronglyMeasurable (X k s) P)
    (hμ : ∀ k, Measurable (Function.uncurry (μ k)))
    (hμint : ∀ k t ω, IntegrableOn (fun s : ℝ => μ k s.toNNReal ω) (Set.Icc 0 (t : ℝ)))
    (hdecomp : ∀ k s, X k s =ᵐ[P] fun ω =>
      X k 0 ω + integratedDrift (μ k) s ω + vectorProcess D (U k) s ω)
    (t : ℝ≥0) :
    TendstoInMeasure P (fun n ω => ∑ k, quadraticLeftSum (X k) t (n + 1) ω) atTop
      (fun ω => (∑ k, X k t ω ^ 2) - (∑ k, X k 0 ω ^ 2) -
        ∑ k, ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U k i) t ω) := by
  have h := tendstoInMeasure_finsetSum Finset.univ
    (fun k n => quadraticLeftSum (X k) t (n + 1))
    (fun k ω => X k t ω ^ 2 - X k 0 ω ^ 2 -
      ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U k i) t ω)
    (fun k _ => quadratic_ito_formula D (U k) (X k) (μ k) (hX k) (hμ k) (hμint k) (hdecomp k) t)
  exact h.congr_right (Eventually.of_forall (fun ω => by
    simp only [Finset.sum_sub_distrib]))

end SphericalAging.VectorItoFormula
