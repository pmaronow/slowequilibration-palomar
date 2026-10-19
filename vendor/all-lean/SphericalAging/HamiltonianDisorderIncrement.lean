module

public import SphericalAging.AffineSecantDifference
public import SphericalAging.HamiltonianPredictableForcing
public import SphericalAging.AffineSDETimeFourthMoment
public import SphericalAging.GlobalHamiltonianParameter

public section

/-! Actual local-in-disorder fourth-moment estimates for constructed
cutoff Hamiltonian process increments, obtained from their genuine bounded
forcing secant SDE. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianDisorderIncrement
open HardSphereDynamics LocalSDE VariationalCoefficients HamiltonianPicardDependence
open HamiltonianPredictableForcing LinearSDETimeFourthMoment
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def increment (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (A : ℝ≥0)
    (J K : BoundedDisorder N p A) (x : State N) (T : ℝ≥0) : ℝ≥0 → Ω → State N :=
  AffineSecantDifference.difference D (drift_family_lipschitz β R hR A J)
    (drift_family_lipschitz β R hR A K) (noise_family_lipschitz N R hR) x T

@[expose]  def fourthConstant (β R : ℝ) (hR : 0 < R) (A T : ℝ≥0) : ℝ :=
  3*(T : ℝ)*(disorderConstant (N := N) (p := p) β R hR : ℝ)^4 *
    Real.exp (AffineSDETimeFourthMoment.momentExponent N
      (driftBound (N := N) (p := p) β R hR A) (noiseBound N R hR) T*T)

 theorem fourthConstant_nonneg (β R : ℝ) (hR : 0 < R) (A T : ℝ≥0) :
    0 ≤ fourthConstant (N := N) (p := p) β R hR A T := by
  unfold fourthConstant
  positivity

/-- The tensor-disorder increment has an actual time-probability L⁴ class
and a genuine bound quartic in the disorder increment, uniformly on every
fixed bounded disorder set. -/
 theorem increment_fourthMoment (D₀ : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (A : ℝ≥0) (J K : BoundedDisorder N p A) (x : State N) (T : ℝ≥0) :
    MemLp (stateTimeCut (increment (NullAugmentation.driver D₀) β R hR A J K x T) T) 4
      (nonnegativeLebesgueMeasure.prod P) ∧
    (∫ q,‖stateTimeCut (increment (NullAugmentation.driver D₀) β R hR A J K x T) T q‖^4
      ∂nonnegativeLebesgueMeasure.prod P) ≤ fourthConstant (N := N) (p := p) β R hR A T*‖K.1-J.1‖^4 := by
  let D := NullAugmentation.driver D₀
  let hj := drift_family_lipschitz β R hR A J
  let hk := drift_family_lipschitz β R hR A K
  let hs := noise_family_lipschitz N R hR
  let B : ℝ≥0 := disorderConstant (N := N) (p := p) β R hR*‖K.1-J.1‖₊
  have hB : ∀ i y,‖CutoffSDE.cutoffDrift β K.1 R hR i y-CutoffSDE.cutoffDrift β J.1 R hR i y‖ ≤ B := by
    intro i y
    simpa only [B,NNReal.coe_mul,coe_nnnorm] using scalar_disorder_bound β J.1 K.1 R hR i y
  have hsol := AffineSecantDifference.difference_strongSolution D
    (cutoffDrift_contDiff β K.1 R hR) (cutoffNoise_contDiff R hR) hj hk hs hB x T
  have h4 := AffineSDETimeFourthMoment.affine_solution_time_fourthMoment_augmented F hsol
  refine ⟨h4.1,?_⟩
  calc
    _ ≤ (T : ℝ)*AffineSDETimeFourthMoment.momentConstant N
        (driftBound (N := N) (p := p) β R hR A) (noiseBound N R hR) B T 0 := h4.2
    _ = _ := by
      rw [AffineSDETimeFourthMoment.momentConstant_zero]
      simp only [B,NNReal.coe_mul,coe_nnnorm,fourthConstant]
      ring
end SphericalAging.HamiltonianDisorderIncrement
