module

public import SphericalAging.ActualSphereMarkovProperty
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

public section

/-! Genuine Feller continuity of the actual Hamiltonian transition
expectations, proved from true terminal L² dependence and bounded continuous
observable expectations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereFeller
open HardSphereDynamics LocalSDE ActualSphereTransition GaussianObservableDerivative
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Bounded continuous observables have a genuine continuous expectation
functional on the actual L² state space. -/
theorem observable_continuous (f : State N → ℝ) (hf : Continuous f)
    (C : ℝ≥0) (hC : ∀ x,‖f x‖ ≤ C) :
    Continuous (observable (P := P) f) := by
  apply continuous_iff_seqContinuous.mpr
  intro u U hu
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hm := tendstoInMeasure_of_tendsto_Lp (hu.comp hns)
  obtain ⟨ms,hms,hmae⟩ := hm.exists_seq_tendsto_ae
  refine ⟨ms,?_⟩
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (C : ℝ))
  · intro n
    exact hf.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (u (ns (ms n))))
  · exact integrable_const _
  · intro n
    exact .of_forall (fun ω => hC _)
  · exact hmae.mono (fun ω hω => hf.continuousAt.tendsto.comp hω)

/-- Actual transition expectation agrees with the genuine adapted terminal
L² class, rather than an independently supplied parameter family. -/
lemma transition_eq_observable_class (D : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (t : ℝ≥0)
    (f : State N → ℝ) (q : FiniteModel.Disorder N p × State N) :
    transition D β R hR q.1 t f q.2 = observable f
      (HamiltonianJointProcess.stateClass D β R hR (GlobalSDE.integerHorizon (Nat.ceil t)) t q :
        Lp (State N) 2 P) := by
  rw [transition_eq_actual]
  apply integral_congr_ae
  have he := HamiltonianJointProcess.stateClass_ae D β R hR
    (GlobalSDE.integerHorizon (Nat.ceil t)) t q
  change _ =ᵐ[P] HamiltonianJointProcess.globalProcess D β R hR q t at he
  exact he.symm.mono (fun ω hω => congrArg f hω)

/-- The genuine transition is jointly continuous in unrestricted disorder
and initial state for every bounded continuous observable. -/
theorem transition_joint_continuous (D : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (t : ℝ≥0)
    (f : State N → ℝ) (hf : Continuous f) (C : ℝ≥0) (hC : ∀ x,‖f x‖ ≤ C) :
    Continuous (fun q : FiniteModel.Disorder N p × State N => transition D β R hR q.1 t f q.2) := by
  have he : (fun q : FiniteModel.Disorder N p × State N => transition D β R hR q.1 t f q.2) =
      fun q => observable f
        (HamiltonianJointProcess.stateClass D β R hR (GlobalSDE.integerHorizon (Nat.ceil t)) t q :
          Lp (State N) 2 P) := funext (transition_eq_observable_class D β R hR t f)
  rw [he]
  exact (observable_continuous f hf C hC).comp (continuous_subtype_val.comp
    (HamiltonianJointProcess.stateClass_continuous D β R hR _ t))

/-- The actual transition preserves bounded continuous observables. -/
theorem transition_continuous (D : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (J : FiniteModel.Disorder N p) (t : ℝ≥0)
    (f : State N → ℝ) (hf : Continuous f) (C : ℝ≥0) (hC : ∀ x,‖f x‖ ≤ C) :
    Continuous (transition D β R hR J t f) :=
  (transition_joint_continuous D β R hR t f hf C hC).comp (continuous_const.prodMk continuous_id)

end SphericalAging.ActualSphereFeller
