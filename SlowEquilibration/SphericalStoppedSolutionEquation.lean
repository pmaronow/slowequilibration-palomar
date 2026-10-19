-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC1Dynamics
public import SphericalAging.RandomVectorSDELocalization
public import SphericalAging.RandomSDEConversions
public import SphericalAging.StaticSDEOperators
public import SphericalAging.WholeVectorTerminalEnergy

/-! A genuine stopped matrix-Itô equation for a continuous adapted version
of a finite-dimensional strong solution. The stopping time can depend on the
whole past of the solution. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalStoppedSolutionEquation
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
open SphericalAging
open HardSphereDynamics LocalSDE RandomSDEConversions
open PredictableDriftTime VectorIto ClosedHitStopping StoppedSDE StoppedVectorIto
open RandomVectorSDELocalization CutoffSphere LinearSDELocalization
open StaticSDEOperators
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem localStrongSolution_stopped_equation
    (D : BrownianDriver N P F)
    (b : Fin N → State N → ℝ) (sigma : Fin N → Fin N → State N → ℝ)
    (hb : ∀ i, Continuous (b i)) (hsigma : ∀ i j, Continuous (sigma i j))
    (x : State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hXc : ∀ ω, Continuous (fun t => X t ω))
    (hX : IsLocalStrongSolutionOn b sigma hsigma D x X T)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T) :
    ∃ (A : Fin N → PredictableProcessL2 F P)
      (U : Fin N → Fin N → PredictableProcessL2 F P),
      (∀ i, (A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        fun q => stoppedTimeCoefficient τ T q * b i (X q.1 q.2)) ∧
      (∀ i j, (U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        fun q => stoppedTimeCoefficient τ T q * sigma i j (X q.1 q.2)) ∧
      ∀ t, t ≤ T → ∀ i, (fun ω => (stoppedState X τ t ω) i) =ᵐ[P]
        fun ω => x i + driftVersion (A i) t t ω +
          (vectorProcessLp D (U i) t : Ω → ℝ) ω := by
  have hR := localStrongSolution_to_random hb hX
  obtain ⟨_,hXa,hXcae,A₀,U₀,hA₀,hU₀,heq⟩ := hR
  let A (i : Fin N) := stoppedIntegrand hτ T (A₀ i)
  let U (i j : Fin N) := stoppedIntegrand hτ T (U₀ i j)
  let μ (i : Fin N) := cutDrift b X T i
  let μ' (i : Fin N) := stoppedDrift (μ i) τ
  have hA (i : Fin N) : (A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => stoppedTimeCoefficient τ T q * b i (X q.1 q.2) := by
    filter_upwards [stoppedIntegrand_coe hτ T (A₀ i),hA₀ i] with q hc ha
    rw [hc,ha]
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp [stoppedTimeCoefficient,hq,FourPapersCommon.continuousAdaptedTimeCut]
    · simp [stoppedTimeCoefficient,hq]
  have hU (i j : Fin N) : (U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => stoppedTimeCoefficient τ T q * sigma i j (X q.1 q.2) := by
    filter_upwards [stoppedIntegrand_coe hτ T (U₀ i j),hU₀ i j] with q hc ha
    rw [hc,ha]
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp [stoppedTimeCoefficient,hq,FourPapersCommon.continuousAdaptedTimeCut]
    · simp [stoppedTimeCoefficient,hq]
  have hμsupport (i : Fin N) (q : ℝ≥0 × Ω) (hq : q.1 ∉ Ioc (0 : ℝ≥0) T) :
      μ i q.1 q.2 = 0 := by
    simp [μ,cutDrift,FourPapersCommon.continuousAdaptedTimeCut,hq]
  have hμ'coeff (i : Fin N) (q : ℝ≥0 × Ω) :
      μ' i q.1 q.2 = stoppedTimeCoefficient τ T q * μ i q.1 q.2 := by
    unfold μ' stoppedDrift stoppedTimeCoefficient
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
    · by_cases hs : q.1 ≤ τ q.2 <;> simp [hq,hs]
    · simp [hq,hμsupport i q hq]
  have hA' (i : Fin N) : (A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => μ' i q.1 q.2 := by
    filter_upwards [stoppedIntegrand_coe hτ T (A₀ i),hA₀ i] with q hc ha
    rw [hc,ha]
    exact (hμ'coeff i q).symm
  have hAcut (i : Fin N) : (A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (μ' i) T := by
    filter_upwards [hA' i] with q hq
    rw [hq]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp [FourPapersCommon.continuousAdaptedTimeCut,ht]
    · simp [FourPapersCommon.continuousAdaptedTimeCut,ht,μ',stoppedDrift,hμsupport i q ht]
  have hd (i : Fin N) : ∀ᵐ ω ∂P, ∀ t,
      integratedDrift (μ' i) t ω = driftVersion (A i) T t ω :=
    integratedDrift_eq_of_coe (μ' i) (A i) T
      ((hA' i).symm.trans (cutRepresentative_eq_of_coe (A i) T (μ' i) (hAcut i)).symm)
  have hMchoice (i : Fin N) := exists_continuousModification_vectorProcess D (U₀ i)
  choose M hM using hMchoice
  have hfixed (i : Fin N) (s : ℝ≥0) (hs : s ≤ T) :
      (fun ω => X s ω i) =ᵐ[P] fun ω => X 0 ω i + integratedDrift (μ i) s ω + M i s ω := by
    filter_upwards [heq s hs i,vectorProcessLp_ae_eq D (U₀ i) s,
      (hM i).fixedTime_ae_eq s,hX.initial] with ω he hlp hm h0
    rw [integratedDrift_cutDrift b X T s hs i ω]
    simpa only [h0,hlp,hm] using he
  refine ⟨A,U,hA,hU,?_⟩
  intro t ht i
  have hstop := stopped_equation D hτ T hτT (U₀ i)
    (fun s ω => X s ω i) (μ i) (M i)
    (fun ω => (CutoffSDE.coordinate_lipschitz i).continuous.comp (hXc ω))
    (fun ω => cutDrift_integrable b hb X hXc T i ω)
    (hM i).fixedTime_ae_eq (hM i).continuous_paths (hfixed i) t
  have hd' := hd i
  filter_upwards [hstop,hd',hX.initial,vectorProcessLp_ae_eq D (U i) t]
    with ω hs hdω h0 hUω
  change (X (min t (τ ω)) ω) i = _
  rw [hs,show stoppedDrift (μ i) τ = μ' i from rfl,hdω t,
    WholeVectorTerminalEnergy.driftVersion_prefix (A i) T t ht ω,h0]
  rw [← hUω]

end SlowEquilibration.SphericalStoppedSolutionEquation
