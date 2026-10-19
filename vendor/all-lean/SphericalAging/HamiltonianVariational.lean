module

public import SphericalAging.LinearVariationalSDE
public import SphericalAging.VariationalCoefficients

public section

/-! Genuine finite-N cutoff Hamiltonian variational equations. The
coefficients below are the actual Fréchet derivatives of the manuscript's
cutoff drift and projection noise along an actual adapted continuous state.
Existence and the integrated second-moment bound are proved here; identification
with differentiation of the nonlinear solution is a further theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.HamiltonianVariational
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def driftConstant (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) : ℝ≥0 :=
  (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose

@[expose] def noiseConstant (N : ℕ) (R : ℝ) (hR : 0 < R) : ℝ≥0 :=
  (CutoffSDE.cutoffNoise_lipschitz N R hR).choose

@[expose] def driftRows (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (T : ℝ≥0) (i : Fin N) :
    Coefficient (N := N) (F := F) (P := P) (driftConstant β J R hR) :=
  derivativeRow X hXa hXc (cutoffDrift_contDiff β J R hR i)
    ((CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec i) T

@[expose] def noiseRows (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (R : ℝ) (hR : 0 < R) (T : ℝ≥0) (i j : Fin N) :
    Coefficient (N := N) (F := F) (P := P) (noiseConstant N R hR) :=
  derivativeRow X hXa hXc (cutoffNoise_contDiff R hR i j)
    ((CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec i j) T

@[simp] theorem driftRows_value (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (T : ℝ≥0) (q : ℝ≥0 × Ω) :
    ∀ i, (driftRows X hXa hXc β J R hR T i).value q =
      if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i) (X q.1 q.2) else 0 := fun _ => rfl

@[simp] theorem noiseRows_value (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (R : ℝ) (hR : 0 < R) (T : ℝ≥0) (q : ℝ≥0 × Ω) :
    ∀ i j, (noiseRows X hXa hXc R hR T i j).value q =
      if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j) (X q.1 q.2) else 0 := fun _ _ => rfl

/-- Actual variational SDE solutions and second-moment bounds for the true
cutoff Hamiltonian Jacobian coefficients, on an arbitrary finite horizon. -/
theorem exists_variational_solution_with_secondMoment (D : BrownianDriver N P F)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (T : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ v0 : State N, ∃ Y,
      LinearVariationalSDE.IsStrongSolutionOn (driftRows X hXa hXc β J R hR T)
        (noiseRows X hXa hXc R hR T) D v0 Y T ∧
      (∫ q, ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
        (fun q => Y q.1 q.2) q‖^2 ∂nonnegativeLebesgueMeasure.prod P) ≤ (C : ℝ)^2 * ‖v0‖^2 :=
  LinearVariationalSDE.exists_strongSolution_with_secondMoment D
    (driftRows X hXa hXc β J R hR T) (noiseRows X hXa hXc R hR T) T

/-- The actual constructed nonlinear cutoff Hamiltonian process. -/
@[expose] def baseProcess (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (x0 : State N) : ℝ≥0 → Ω → State N :=
  GlobalSDE.process D (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x0

theorem baseProcess_stronglyAdapted (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (x0 : State N) : StronglyAdapted F (baseProcess D β J R hR x0) :=
  GlobalSDE.process_stronglyAdapted D _ _ x0

theorem baseProcess_continuous (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (x0 : State N) :
    ∀ᵐ omega ∂P, Continuous (fun t => baseProcess D β J R hR x0 t omega) :=
  GlobalSDE.process_continuous D _ _ x0

theorem baseProcess_strongSolution (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (x0 : State N) (T : ℝ≥0) :
    IsLocalStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
      (fun i j => ((CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec i j).continuous)
      D x0 (baseProcess D β J R hR x0) T :=
  GlobalSDE.process_strongSolution D _ _ x0 T

/-- Concrete variational equations along the actual nonlinear solution;
adaptation, continuity and existence of that base solution are proved. -/
theorem exists_cutoff_variational_solution (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (x0 : State N) (T : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ v0 : State N, ∃ Y,
      LinearVariationalSDE.IsStrongSolutionOn
        (driftRows (baseProcess D β J R hR x0) (baseProcess_stronglyAdapted D β J R hR x0)
          (baseProcess_continuous D β J R hR x0) β J R hR T)
        (noiseRows (baseProcess D β J R hR x0) (baseProcess_stronglyAdapted D β J R hR x0)
          (baseProcess_continuous D β J R hR x0) R hR T) D v0 Y T ∧
      (∫ q, ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
        (fun q => Y q.1 q.2) q‖^2 ∂nonnegativeLebesgueMeasure.prod P) ≤ (C : ℝ)^2 * ‖v0‖^2 :=
  exists_variational_solution_with_secondMoment D _ (baseProcess_stronglyAdapted D β J R hR x0)
    (baseProcess_continuous D β J R hR x0) β J R hR T

end SphericalAging.HamiltonianVariational
