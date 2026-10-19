module

public import SphericalAging.RandomInitialSphere
public import SphericalAging.PhysicalUniqueness

public section

/-! Actual common-path uniqueness for the full-filtration SDE with random
initial data. Predictable state classes of sphere solutions are constructed
from their actual bounded coordinates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.RandomInitialUniqueness
open HardSphereDynamics LocalSDE RandomInitialSDE RandomInitialSphere PredictableItoTime
open PhysicalUniqueness CutoffSphere
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem strongSolution_unique_of_stateClasses (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0)
    {X Y : ℝ≥0 → Ω → State N} {U V : PredictableStateL2 N F P}
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hYeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => Y p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hX : IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0 X T)
    (hY : IsStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D Z0 Y T) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ T → X t omega = Y t omega := by
  have hU := RandomInitialSDE.strongSolution_fixedPoint hXeq D hb hsigma Z0 hZ0 hmem hX
  have hV := RandomInitialSDE.strongSolution_fixedPoint hYeq D hb hsigma Z0 hZ0 hmem hY
  have hUV := (RandomInitialSDE.horizonClass_unique D hb hsigma Z0 hZ0 hmem T U hU).trans
    (RandomInitialSDE.horizonClass_unique D hb hsigma Z0 hZ0 hmem T V hV).symm
  have hx := RandomInitialSDE.strongSolution_eq_version hXeq D hb hsigma Z0 hZ0 hmem hX
  have hy := RandomInitialSDE.strongSolution_eq_version hYeq D hb hsigma Z0 hZ0 hmem hY
  rw [hUV] at hx
  filter_upwards [hx,hy] with omega hxomega hyomega
  intro t ht
  exact (hxomega t ht).trans (hyomega t ht).symm

theorem cutoff_solution_of_physical (D : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (Z0 : Ω → State N) (_hZ0 : StronglyMeasurable[F 0] Z0) (_hmem : MemLp Z0 2 P) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hsol : IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D Z0 X T)
    (hSphere : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω))
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) ≤ (R : ℝ)^2)
    (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j)) :
    IsStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D Z0 X T := by
  have hbound : ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖X t ω‖ ≤ R := by
    filter_upwards [hSphere] with ω hω
    intro t ht
    have hsq := (onSphere_iff_norm_sq (X t ω)).mp (hω t ht)
    nlinarith [norm_nonneg (X t ω), R.coe_nonneg]
  apply RandomInitialSphere.coefficient_congr_onPath hsigma hsol
  · intro i
    filter_upwards [hbound] with ω hω
    intro t ht
    exact CutoffSDE.cutoffDrift_eq β J R hR _ (hω t ht) i
  · intro i j
    filter_upwards [hbound] with ω hω
    intro t ht
    exact CutoffSDE.cutoffNoise_eq N R hR _ (hω t ht) i j

/-- Pathwise uniqueness of the actual finite-N Hamiltonian sphere SDE on
any finite horizon. Both solution premises contain the actual full
filtration matrix Itô equation; their state classes and the uniqueness
argument are constructed from the genuine sphere bound. -/
theorem physical_pathwise_uniqueness (D : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0)
    (X Y : ℝ≥0 → Ω → State N)
    (hX : IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D Z0 X T)
    (hY : IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D Z0 Y T)
    (hXs : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω))
    (hYs : ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (Y t ω)) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → X t ω = Y t ω := by
  let R : ℝ≥0 := N + 1
  have hR : 0 < (R : ℝ) := by simp only [R, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]; positivity
  have hNR : (N : ℝ) ≤ (R : ℝ)^2 := by
    simp only [R, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    nlinarith [sq_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨Kb, hb⟩ := CutoffSDE.cutoffDrift_lipschitz β J R hR
  obtain ⟨Ks, hsigma⟩ := CutoffSDE.cutoffNoise_lipschitz N R hR
  have hXcut := cutoff_solution_of_physical D β J Z0 hZ0 hmem X T hX hXs R hR hNR (fun i j => (hsigma i j).continuous)
  have hYcut := cutoff_solution_of_physical D β J Z0 hZ0 hmem Y T hY hYs R hR hNR (fun i j => (hsigma i j).continuous)
  obtain ⟨hXa, hXc, hbmX, hsmX, hEqX⟩ := hX
  obtain ⟨hYa, hYc, hbmY, hsmY, hEqY⟩ := hY
  exact strongSolution_unique_of_stateClasses D hb hsigma Z0 hZ0 hmem T
    (boundedStateClass_coe X hXa hXc R T (sphere_radius_bound X T hXs))
    (boundedStateClass_coe Y hYa hYc R T (sphere_radius_bound Y T hYs)) hXcut hYcut

/-- On a common Brownian driver, two actual global sphere solutions agree
simultaneously for every time. Countability of integer horizons supplies
one common null event, rather than a separate exceptional event per time. -/
theorem physical_global_pathwise_uniqueness (D : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (X Y : ℝ≥0 → Ω → State N)
    (hX : ∀ T, IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D Z0 X T)
    (hY : ∀ T, IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D Z0 Y T)
    (hXs : ∀ᵐ ω ∂P, ∀ t, OnSphere (X t ω))
    (hYs : ∀ᵐ ω ∂P, ∀ t, OnSphere (Y t ω)) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t, t ≤ (n : ℝ≥0) → X t ω = Y t ω := by
    apply ae_all_iff.mpr
    intro n
    exact physical_pathwise_uniqueness D β J Z0 hZ0 hmem n X Y (hX n) (hY n)
      (hXs.mono (fun ω hω t _ => hω t)) (hYs.mono (fun ω hω t _ => hω t))
  filter_upwards [hall] with ω hω
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact hω n t hn

end SphericalAging.RandomInitialUniqueness
