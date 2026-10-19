module

public import SphericalAging.AnnealedSphereProcess
public import SphericalAging.SphereSurfaceIdentification

public section

/-! The complete finite-N disorder/initial/Brownian product probability
model used by the annealed SDE. The whole finite Gaussian disorder second
moment is derived from the actual Gaussian coordinate laws. Initial law is
the proved normalized surface measure on the physical sphere.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.AnnealedModelLaw
open HardSphereDynamics AnnealedCutoffProcess FiniteModel
set_option maxHeartbeats 1000000

/-- The actual complete finite Gaussian tensor, with its finite Pi norm,
has a second moment under the literal product Gaussian law. -/
theorem disorder_memLp (N p : ℕ) :
    MemLp (id : Disorder N p → Disorder N p) 2 (disorderLaw N p) := by
  have hm : MemLp (fun J : Disorder N p => ∑ I : TensorIndex N p,
      J I • HamiltonianParameter.disorderBasis I) 2 (disorderLaw N p) :=
    memLp_finsetSum Finset.univ (fun I _ => by
      simpa only [Function.comp_def,ContinuousLinearMap.toSpanSingleton_apply] using
        (ContinuousLinearMap.toSpanSingleton ℝ (HamiltonianParameter.disorderBasis I)).comp_memLp'
          (coordinate_memLp N p I))
  convert hm using 1
  funext J
  exact (HamiltonianParameter.disorder_sum_basis J).symm

/-- Independent actual Gaussian disorder and normalized-surface initial law. -/
@[expose] def parameterLaw (N p : ℕ) : Measure (Parameter N p) :=
  (disorderLaw N p).prod (SphereInitialLaw.sphereLaw N)

instance parameterLaw_probability (N p : ℕ) : IsProbabilityMeasure (parameterLaw N p) := by
  unfold parameterLaw
  infer_instance

/-- Complete independent parameter and continuous-vector Brownian sample law. -/
@[expose] def law (N p : ℕ) : Measure (Parameter N p × VectorBrownian.Space N) :=
  (parameterLaw N p).prod (VectorBrownian.law N)

instance law_probability (N p : ℕ) : IsProbabilityMeasure (law N p) := by
  unfold law
  infer_instance

@[expose] def filtration (N p : ℕ) := IndependentBackgroundDriver.filtration (Parameter N p)
  (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N))

/-- Constructed independent Brownian driver in the full background-augmented
vector filtration, with genuine joint future-increment independence. -/
@[expose] def driver (N p : ℕ) : BrownianDriver N (law N p) (filtration N p) :=
  IndependentBackgroundDriver.driver (ρ := parameterLaw N p)
    (NullAugmentation.driver (VectorBrownian.driver N))

theorem parameter_disorder_memLp (N p : ℕ) :
    MemLp (fun q : Parameter N p => q.1) 2 (parameterLaw N p) :=
  (disorder_memLp N p).comp_measurePreserving
    (measurePreserving_fst (μ := disorderLaw N p) (ν := SphereInitialLaw.sphereLaw N))

theorem parameter_initial_onSphere {N : ℕ} (hN : 1 ≤ N) (p : ℕ) :
    ∀ᵐ q ∂parameterLaw N p, OnSphere q.2 := by
  have h := (Measure.quasiMeasurePreserving_snd (μ := disorderLaw N p) (ν := SphereInitialLaw.sphereLaw N)).ae
    (SphereInitialLaw.sphereLaw_support hN)
  filter_upwards [h] with q hq
  exact (onSphere_iff_norm_sq q.2).mpr hq

theorem parameter_initial_memLp {N : ℕ} (hN : 1 ≤ N) (p : ℕ) :
    MemLp (fun q : Parameter N p => q.2) 2 (parameterLaw N p) :=
  (SphereInitialLaw.sphereLaw_memLp hN 2).comp_measurePreserving
    (measurePreserving_snd (μ := disorderLaw N p) (ν := SphereInitialLaw.sphereLaw N))

end SphericalAging.AnnealedModelLaw
