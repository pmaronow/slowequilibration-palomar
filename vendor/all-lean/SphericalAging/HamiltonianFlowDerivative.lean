module

public import SphericalAging.StochasticFlowDerivative
public import SphericalAging.HamiltonianVariational

public section

/-! The actual finite-N cutoff Hamiltonian solution has a proved Fréchet
initial-state derivative, identified with the genuine predictable Jacobian
matrix SDE. No derivative identification is supplied as a hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianFlowDerivative
open HardSphereDynamics LocalSDE VariationalCoefficients SecantCoefficient
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem cutoffDrift_derivative_uniform_lipschitz (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) : ∃ L : ℝ≥0,∀ i : Fin N,
      LipschitzWith L (fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i)) := by
  classical
  choose L hL using (fun i : Fin N => cutoffDrift_derivative_lipschitz β J R hR i)
  refine ⟨∑ i,L i,fun i => (hL i).weaken ?_⟩
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)

 theorem cutoffNoise_derivative_uniform_lipschitz (R : ℝ) (hR : 0 < R) :
    ∃ L : ℝ≥0,∀ i j : Fin N, LipschitzWith L (fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j)) := by
  classical
  choose L hL using (fun q : Fin N × Fin N => cutoffNoise_derivative_lipschitz R hR q.1 q.2)
  refine ⟨∑ q,L q,fun i j => (hL (i,j)).weaken ?_⟩
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ (i,j))

@[expose]  def flowClass (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (x : State N) (T : ℝ≥0) : PredictableStateL2 N F P :=
  GlobalSDE.horizonClass D (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T

@[expose]  def flowResponse (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (x : State N) (T : ℝ≥0) : State N →L[ℝ] PredictableStateL2 N F P :=
  StochasticFlowDerivative.response D (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T

/-- Genuine initial-state Fréchet derivative of the actual cutoff
Hamiltonian SDE solution class on every positive finite horizon. -/
 theorem flowClass_hasFDerivAt_initial (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R)
    (x : State N) (T : ℝ≥0) (hT : 0 < T) :
    HasFDerivAt (fun y : State N => flowClass (NullAugmentation.driver D₀) β J R hR y T)
      (flowResponse (NullAugmentation.driver D₀) β J R hR x T) x := by
  obtain ⟨Lb,hb⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hs⟩ := cutoffNoise_derivative_uniform_lipschitz (N := N) R hR
  exact StochasticFlowDerivative.horizonClass_hasFDerivAt_initial D₀
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec hb hs x T hT

/-- The identified derivative class has an actual adapted continuous
strong variational-SDE representative, with the true cutoff Jacobians. -/
 theorem exists_flowResponse_solution (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R)
    (x v : State N) (T : ℝ≥0) : ∃ Y,
      LinearVariationalSDE.IsStrongSolutionOn
        (StochasticFlowDerivative.driftRows D (cutoffDrift_contDiff β J R hR)
          (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
          (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T)
        (StochasticFlowDerivative.noiseRows D (cutoffNoise_contDiff R hR)
          (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
          (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T) D v Y T ∧
      ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => Y q.1 q.2))
        =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (flowResponse D β J R hR x T v : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  let a := StochasticFlowDerivative.driftRows D (cutoffDrift_contDiff β J R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T
  let s := StochasticFlowDerivative.noiseRows D (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T
  let U := LinearVariationalSDE.sourceClass D a s T (initialClass v T)
  have hU := LinearVariationalSDE.sourceClass_fixedPoint D a s T (initialClass v T)
  exact ⟨LinearVariationalSDE.version D a s v T U,
    LinearVariationalSDE.strongSolution_of_fixedPoint D a s v T U hU,
    LinearVariationalSDE.version_timeCut_eq_fixedPoint_ae D a s v T U hU⟩
end SphericalAging.HamiltonianFlowDerivative
