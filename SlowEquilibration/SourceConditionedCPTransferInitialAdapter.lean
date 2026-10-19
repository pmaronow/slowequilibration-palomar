-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionConsumerAsymptotic
public import SlowEquilibration.SphericalHaarTransferAsymptotics
public import SlowEquilibration.SphericalIndependentInitialTransfer

/-! The literal original-uniform consumer conclusion is identified with the
existing Haar-transfer premise. Consequently its exponential horizon applies
uniformly to every prescribed field-independent initial law, and to an
initial law sampled independently of the full tensor field. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceConditionedCPTransferInitialAdapter

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalOrthogonalHaar
open SphericalAging.HardSphereDynamics
open SourceReductionConsumerAsymptotic
open scoped Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The source consumer uses dimensions `n+2`; the Haar reduction uses
the ordinary dimension index. These are the same convergence statement,
including the actual all-time infimum and full tensor-disorder law. -/
theorem original_uniform_to_haar (μ : FiniteMixture) (β : ℝ)
    (T : ℕ → ℝ≥0)
    (h : VaryingConvergesInProbability
      (fun n => disorderLaw (n+2) μ.maxDegree)
      (fun n => originalUniformIntervalDistance μ β (T (n+2)))
      (fun _ _ => 1)) :
    uniformSeparationInProbability μ β T := by
  intro ε hε
  have heq (n : ℕ) (J : Disorder (n+2) μ.maxDegree) :
      intervalDistance μ β (T (n+2)) J (uniformInitialProbability (n+2)) =
        originalUniformIntervalDistance μ β (T (n+2)) J := by
    rw [intervalDistance_eq_endpoint (by omega : 1 ≤ n+2),
      originalUniformIntervalDistance_eq_endpoint (by omega : 1 ≤ n+2)]
    unfold distance uniformInitialProbability
    rfl
  have hs : Tendsto (fun n =>
      (disorderLaw (n+2) μ.maxDegree).real
        {J | ε ≤ ‖intervalDistance μ β (T (n+2)) J
          (uniformInitialProbability (n+2)) - 1‖}) atTop (𝓝 0) := by
    convert h ε hε using 1
    funext n
    congr 1
    ext J
    simp only [Set.mem_ofPred_eq, heq]
  exact (tendsto_add_atTop_iff_nat 2).mp hs

/-- Source main-initial (i), deterministic clause, as a direct corollary of
the uniform-start consumer. The supremum remains outside the probability. -/
theorem prescribed_initial_failure_of_original_uniform
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (h : VaryingConvergesInProbability
      (fun n => disorderLaw (n+2) μ.maxDegree)
      (fun n => originalUniformIntervalDistance μ β (T (n+2)))
      (fun _ _ => 1)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (uniformPrescribedFailure μ β T ε) atTop (𝓝 0) :=
  uniformPrescribedFailure_tendsto_zero μ β T
    (original_uniform_to_haar μ β T h) hε

/-- Source main-initial (i), independent random clause, on genuinely
dimension-dependent sample spaces with a proved independence hypothesis. -/
theorem independent_initial_failure_of_original_uniform
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (h : VaryingConvergesInProbability
      (fun n => disorderLaw (n+2) μ.maxDegree)
      (fun n => originalUniformIntervalDistance μ β (T (n+2)))
      (fun _ _ => 1))
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (J : ∀ N, Ω N → Disorder N μ.maxDegree)
    (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N))
    (hJ : ∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N))
    (hν : ∀ N, AEMeasurable (ν N) (P N))
    (hind : ∀ N, IndepFun (J N) (ν N) (P N))
    (hsphere : ∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ x ∂(ν N ω).toMeasure, OnSphere x)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => (P N).real
      {ω | intervalDistance μ β (T N) (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0) :=
  independent_sampled_initial_failure_tendsto_zero μ β T
    (original_uniform_to_haar μ β T h) P J ν hJ hν hind hsphere hε

end SlowEquilibration.SourceConditionedCPTransferInitialAdapter
