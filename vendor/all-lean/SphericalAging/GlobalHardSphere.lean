module

public import SphericalAging.GlobalSDE
public import SphericalAging.CutoffSphere
public import SphericalAging.VectorBrownian

public section

/-! Global nonexplosive finite-N hard-sphere Hamiltonian dynamics. The
compact cutoff is constructed on arbitrary horizons, the horizon solutions
are proved compatible, and radial Itô plus zero uniqueness removes the
cutoff. Sphere preservation and global existence are theorem conclusions. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.GlobalHardSphere
open HardSphereDynamics LocalSDE
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual all-path continuous global solution on the constructed null
augmentation, preserving every actual stochastic integral equation. -/
theorem exists_allPath_global_strongSolution (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) : ∃ X : ℝ≥0 → Ω → State N,
      (∀ omega, Continuous (fun t => X t omega)) ∧
      ∀ T : ℝ≥0, IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous)
        (NullAugmentation.driver D) x0 X T := by
  obtain ⟨X,hXa,hXc,hXsol⟩ := GlobalSDE.exists_global_strongSolution (NullAugmentation.driver D) hb hsigma x0
  obtain ⟨Y,hYa,hYc,hYX⟩ := NullAugmentation.exists_allPath_continuous_modification_augmented F X hXa hXc
  refine ⟨Y,hYc,fun T => ?_⟩
  exact AllPathSDE.IsLocalStrongSolutionOn.path_congr (hXsol T) hYa (.of_forall hYc) hYX

theorem exists_allPath_global_cutoff_hamiltonian_strongSolution (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R) (x0 : State N) :
    ∃ X : ℝ≥0 → Ω → State N, (∀ omega, Continuous (fun t => X t omega)) ∧
      ∃ hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j),
        ∀ T : ℝ≥0, IsLocalStrongSolutionOn (CutoffSDE.cutoffDrift β J R hR) (CutoffSDE.cutoffNoise N R hR)
          hsigma (NullAugmentation.driver D) x0 X T := by
  obtain ⟨Kb,hb⟩ := CutoffSDE.cutoffDrift_lipschitz β J R hR
  obtain ⟨Ks,hsigma⟩ := CutoffSDE.cutoffNoise_lipschitz N R hR
  obtain ⟨X,hXc,hXsol⟩ := exists_allPath_global_strongSolution D hb hsigma x0
  exact ⟨X,hXc,(fun i j => (hsigma i j).continuous),hXsol⟩

/-- The manuscript's untruncated finite-N hard-sphere Hamiltonian SDE has a
global nonexplosive strongly adapted solution. On one common probability-one
path event it stays on the sphere at every nonnegative time. -/
theorem exists_global_physical_hamiltonian_strongSolution (hN : N ≠ 0)
    (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (x0 : State N) (hx0 : OnSphere x0) :
    ∃ X : ℝ≥0 → Ω → State N, (∀ omega, Continuous (fun t => X t omega)) ∧
      (∀ T : ℝ≥0, IsLocalStrongSolutionOn (fun i x => hamiltonianDrift β J x i)
        (fun i j x => noiseColumn x j i) CutoffSphere.physical_noise_continuous
        (NullAugmentation.driver D) x0 X T) ∧
      (∀ᵐ omega ∂P, ∀ t, OnSphere (X t omega)) := by
  let R : ℝ≥0 := N+1
  have hR : 0 < (R : ℝ) := by simp only [R,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]; positivity
  have hNR : (N : ℝ) < (R : ℝ)^2 := by
    simp only [R,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    nlinarith [sq_nonneg (N : ℝ),Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨X,hXc,hsigma,hXsol⟩ := exists_allPath_global_cutoff_hamiltonian_strongSolution D β J R hR x0
  have hphysical := fun T => CutoffSphere.physical_solution_of_cutoff hN (NullAugmentation.driver D)
    β J R hR hNR x0 hx0 X hXc T hsigma (hXsol T)
  refine ⟨X,hXc,(fun T => (hphysical T).1),?_⟩
  have hall := ae_all_iff.mpr (fun n : ℕ => (hphysical (GlobalSDE.integerHorizon n)).2)
  filter_upwards [hall] with omega homega
  intro t
  exact homega (Nat.ceil t) t (GlobalSDE.le_integerHorizon_ceil t)

/-- Concrete Brownian-path probability-model corollary. The independent
vector Brownian driver and its full joint filtration are constructed, so
even the driving process is not an existence hypothesis. -/
theorem exists_global_physical_on_brownian_paths (hN : N ≠ 0) (β : ℝ)
    (J : FiniteModel.Disorder N p) (x0 : State N) (hx0 : OnSphere x0) :
    ∃ X : ℝ≥0 → VectorBrownian.Space N → State N,
      (∀ omega, Continuous (fun t => X t omega)) ∧
      (∀ T : ℝ≥0, IsLocalStrongSolutionOn (fun i x => hamiltonianDrift β J x i)
        (fun i j x => noiseColumn x j i) CutoffSphere.physical_noise_continuous
        (NullAugmentation.driver (VectorBrownian.driver N)) x0 X T) ∧
      (∀ᵐ omega ∂VectorBrownian.law N, ∀ t, OnSphere (X t omega)) :=
  exists_global_physical_hamiltonian_strongSolution hN (VectorBrownian.driver N) β J x0 hx0

end SphericalAging.GlobalHardSphere
