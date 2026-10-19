module

public import SphericalAging.MultivariateItoSums
public import SphericalAging.SDEWeightedLinear

public section

/-! Actual compactly supported derivative weights for a C² observable.
They agree with the derivative on the physical state ball and supply true
bounded predictable Itô products even on exceptional sample paths. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.MultivariateItoWeights
open HardSphereDynamics LocalSDE MultivariateTaylor MultivariateItoSums
open WeightedItoSums
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

@[expose] def derivativeWeight (f : State N → ℝ) (R : ℝ) (hR : 0<R) (i : Fin N) (x : State N) : ℝ :=
  coefficientBump (N := N) R hR x*fderiv ℝ f x (basisVector i)

lemma derivative_basis_continuous {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin N) :
    Continuous (fun x => fderiv ℝ f x (basisVector i)) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma derivativeWeight_continuous {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (R : ℝ) (hR : 0<R) (i : Fin N) : Continuous (derivativeWeight f R hR i) :=
  (coefficientBump (N := N) R hR).continuous.mul (derivative_basis_continuous hf i)

lemma derivativeWeight_bounded {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (R : ℝ) (hR : 0<R) (i : Fin N) : ∃ K : ℝ≥0,∀ x,‖derivativeWeight f R hR i x‖≤K := by
  have hs : HasCompactSupport (derivativeWeight f R hR i) :=
    (coefficientBump (N := N) R hR).hasCompactSupport.mul_right
  obtain ⟨K,hK⟩ := hs.exists_bound_of_continuous (derivativeWeight_continuous hf R hR i)
  exact ⟨Real.toNNReal K,fun x => (hK x).trans (Real.le_coe_toNNReal K)⟩

lemma derivativeWeight_eq (f : State N → ℝ) (R : ℝ) (hR : 0<R)
    (i : Fin N) (x : State N) (hx : ‖x‖≤R) :
    derivativeWeight f R hR i x=fderiv ℝ f x (basisVector i) := by
  have hm : x ∈ Metric.closedBall (0 : State N) (coefficientBump (N := N) R hR).rIn := by
    simpa only [coefficientBump,Metric.mem_closedBall,dist_zero_right] using hx
  simp only [derivativeWeight,(coefficientBump (N := N) R hR).one_of_mem_closedBall hm,one_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma weight_stronglyAdapted {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (R : ℝ) (hR : 0<R) (i : Fin N) {X : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) :
    StronglyAdapted F (fun s ω => derivativeWeight f R hR i (X s ω)) := by
  intro s
  exact (derivativeWeight_continuous hf R hR i).comp_stronglyMeasurable (hXa s)

lemma weight_continuous {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (R : ℝ) (hR : 0<R) (i : Fin N) {X : ℝ≥0 → Ω → State N}
    (hXc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω)) :
    ∀ᵐ ω ∂P,Continuous (fun s => derivativeWeight f R hR i (X s ω)) :=
  hXc.mono (fun _ hc => (derivativeWeight_continuous hf R hR i).comp hc)

/-- On every genuine bounded physical path, the finite first-order Taylor
sum is exactly the sum of the bounded derivative coordinate left sums. -/
lemma linearApprox_eq_weightedLeftSum (f : State N → ℝ) (R : ℝ) (hR : 0<R)
    (X : ℝ≥0 → Ω → State N) (hXb : ∀ᵐ ω ∂P,∀ s,‖X s ω‖≤R)
    (t : ℝ≥0) (n : ℕ) :
    linearApprox f X t n =ᵐ[P] fun ω => ∑ i : Fin N,weightedLeftSum
      (fun s ω => derivativeWeight f R hR i (X s ω)) (fun s ω => X s ω i) t n ω := by
  filter_upwards [hXb] with ω hω
  unfold linearApprox weightedLeftSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← state_sum_basis (X (uniformPartitionTime t n (l+1)) ω-X (uniformPartitionTime t n l) ω)]
  simp only [map_sum,map_smul,smul_eq_mul,PiLp.sub_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivativeWeight_eq f R hR i _ (hω _)]
  ring

end SphericalAging.MultivariateItoWeights
