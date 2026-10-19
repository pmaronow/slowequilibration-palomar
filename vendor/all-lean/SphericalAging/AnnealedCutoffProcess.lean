module

public import SphericalAging.HamiltonianFamilyIntegrability
public import SphericalAging.HamiltonianJointProcess
public import SphericalAging.ParameterizedDriftLift
public import SphericalAging.ParameterizedItoVersion

public section

/-! The actual annealed cutoff process is constructed from the independent
background product law and the genuine product-filtration drift and Itô
operators. Its parameter sections are identified with the true deterministic
Hamiltonian Picard solutions. Continuity on the product probability space is
proved from the actual continuous integral versions.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.AnnealedCutoffProcess
open HardSphereDynamics LocalSDE PredictableDriftTime PredictableItoTime
open IndependentBackgroundDriver HamiltonianCoefficientDependence HamiltonianFamilyIntegrability
open HamiltonianPicardDependence GlobalHamiltonianParameter
set_option maxHeartbeats 2000000
variable {N p : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
@[expose] abbrev Parameter (N p : ℕ) := FiniteModel.Disorder N p × State N
variable {ρ : Measure (Parameter N p)} [IsProbabilityMeasure ρ]

/-- Actual outer L² class of the nonlinear drift coefficients. -/
@[expose] def driftFamily (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i : Fin N) :
    Lp (PredictableProcessL2 F P) 2 ρ :=
  (driftClass_memLp D β R hR T i hJ).toLp (driftClass D β R hR T i)

/-- Actual outer L² class of the nonlinear matrix-noise coefficients. -/
@[expose] def noiseFamily (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (T : ℝ≥0) (i j : Fin N) : Lp (PredictableProcessL2 F P) 2 ρ :=
  (noiseClass_memLp D β R hR T i j).toLp (noiseClass D β R hR T i j)

@[expose] def driftLift (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i : Fin N) :
    PredictableProcessL2 (filtration (Parameter N p) F) (ρ.prod P) :=
  PredictableFamilyLift.familyLift (driftFamily D β R hR hJ T i)

@[expose] def noiseLift (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (T : ℝ≥0) (i j : Fin N) :
    PredictableProcessL2 (filtration (Parameter N p) F) (ρ.prod P) :=
  PredictableFamilyLift.familyLift (noiseFamily D β R hR T i j)

/-- The genuine enlarged-filtration continuous scalar integral version. -/
@[expose] def coordinateProcess (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i : Fin N)
    (t : ℝ≥0) (ω : Parameter N p × Ω) : ℝ :=
  ω.1.2 i + driftVersion (driftLift D β R hR hJ T i) T t ω +
    ∑ j : Fin N, itoVersion ((driver (ρ := ρ) D).brownian j)
      ((driver (ρ := ρ) D).coordinateStronglyMeasurable j) ((driver (ρ := ρ) D).filtered j)
      (noiseLift D β R hR T i j) t ω

/-- Actual state-valued annealed cutoff process on a finite horizon. -/
@[expose] def process (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0)
    (t : ℝ≥0) (ω : Parameter N p × Ω) : State N :=
  ∑ i : Fin N, coordinateProcess D β R hR hJ T i t ω • basisVector i

lemma coordinateProcess_stronglyAdapted (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i : Fin N) :
    StronglyAdapted (filtration (Parameter N p) F) (coordinateProcess D β R hR hJ T i) := by
  intro t
  apply StronglyMeasurable.add
  · apply StronglyMeasurable.add
    · exact ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).stronglyMeasurable.comp_measurable
        (measurable_snd.comp (background_known t)))
    · exact driftVersion_stronglyAdapted _ T t
  · exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun j _ =>
      itoVersion_stronglyAdapted ((driver (ρ := ρ) D).brownian j)
        ((driver (ρ := ρ) D).coordinateStronglyMeasurable j) ((driver (ρ := ρ) D).filtered j) _ t)

lemma process_stronglyAdapted (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) :
    StronglyAdapted (filtration (Parameter N p) F) (process D β R hR hJ T) := by
  intro t
  exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
    (coordinateProcess_stronglyAdapted D β R hR hJ T i t).smul_const (basisVector i))

lemma coordinateProcess_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) (i : Fin N) :
    ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => coordinateProcess D β R hR hJ T i t ω) := by
  have hall : ∀ᵐ ω ∂ρ.prod P, ∀ j : Fin N, Continuous (fun t => itoVersion
      ((driver (ρ := ρ) D).brownian j) ((driver (ρ := ρ) D).coordinateStronglyMeasurable j)
      ((driver (ρ := ρ) D).filtered j) (noiseLift D β R hR T i j) t ω) :=
    ae_all_iff.mpr (fun j => (itoVersion_continuousModification ((driver (ρ := ρ) D).brownian j)
      ((driver (ρ := ρ) D).coordinateStronglyMeasurable j) ((driver (ρ := ρ) D).filtered j) _).continuous_paths)
  filter_upwards [driftVersion_ae_continuous (driftLift D β R hR hJ T i) T,hall] with ω hd hn
  exact (continuous_const.add hd).add (continuous_finsetSum Finset.univ (fun j _ => hn j))

lemma process_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) :
    ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => process D β R hR hJ T t ω) := by
  filter_upwards [ae_all_iff.mpr (fun i => coordinateProcess_continuous D β R hR hJ T i)] with ω hc
  exact continuous_finsetSum Finset.univ (fun i _ => (hc i).smul continuous_const)

lemma coordinateProcess_slice (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T t : ℝ≥0) (i : Fin N) :
    ∀ᵐ q ∂ρ, (fun ω => coordinateProcess D β R hR hJ T i t (q,ω)) =ᵐ[P]
      coordinateVersion D (drift_family_lipschitz β R hR (‖q.1‖₊+1) (⟨q.1,by simp⟩))
        (noise_family_lipschitz N R hR) q.2 T (globalClass D β R hR T q) i t := by
  have hd := ParameterizedDriftLift.driftVersion_familyLift T (driftFamily D β R hR hJ T i)
  have hn : ∀ᵐ q ∂ρ, ∀ j : Fin N,
      (fun ω => itoVersion ((driver (ρ := ρ) D).brownian j)
        ((driver (ρ := ρ) D).coordinateStronglyMeasurable j) ((driver (ρ := ρ) D).filtered j)
        (noiseLift D β R hR T i j) t (q,ω)) =ᵐ[P]
      itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (noiseFamily D β R hR T i j q) t :=
    ae_all_iff.mpr (fun j => ParameterizedItoVersion.itoVersion_familyLift_slice D j (noiseFamily D β R hR T i j) t)
  have hnf : ∀ᵐ q ∂ρ, ∀ j : Fin N,
      noiseFamily D β R hR T i j q = noiseClass D β R hR T i j q :=
    ae_all_iff.mpr (fun j => (noiseClass_memLp (ρ := ρ) D β R hR T i j).coeFn_toLp)
  filter_upwards [hd,hn,hnf,(driftClass_memLp D β R hR T i hJ).coeFn_toLp] with q hd hn hnf hdf
  have hna := ae_all_iff.mpr hn
  filter_upwards [hd,hna] with ω hd hn
  have hd' : driftVersion (driftLift D β R hR hJ T i) T t (q,ω) =
      driftVersion (driftClass D β R hR T i q) T t ω :=
    (hd t).trans (congrArg (fun U => driftVersion U T t ω) hdf)
  have hn' (j : Fin N) : itoVersion ((driver (ρ := ρ) D).brownian j)
      ((driver (ρ := ρ) D).coordinateStronglyMeasurable j) ((driver (ρ := ρ) D).filtered j)
      (noiseLift D β R hR T i j) t (q,ω) =
      itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (noiseClass D β R hR T i j q) t ω :=
    (hn j).trans (congrArg (fun U => itoVersion (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) U t ω) (hnf j))
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl hd')
    (Finset.sum_congr rfl (fun j _ => hn' j))

/-- At every terminal time the actual product process has the genuine
deterministic-parameter Hamiltonian solution as its parameter sections. -/
theorem process_slice (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T t : ℝ≥0) :
    ∀ᵐ q ∂ρ, (fun ω => process D β R hR hJ T t (q,ω)) =ᵐ[P]
      HamiltonianJointProcess.process D β R hR T q t := by
  filter_upwards [ae_all_iff.mpr (fun i => coordinateProcess_slice D β R hR hJ T t i)] with q hq
  filter_upwards [ae_all_iff.mpr hq] with ω hω
  unfold process HamiltonianJointProcess.process GlobalSDE.horizonProcess version
  simp only [hω]
  rfl

/-- On almost every parameter section, one common path event identifies
the actual product process and the genuine canonical solution at all times. -/
theorem process_slice_allTimes (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) :
    ∀ᵐ q ∂ρ, ∀ᵐ ω ∂P, ∀ t, process D β R hR hJ T t (q,ω) =
      HamiltonianJointProcess.process D β R hR T q t ω := by
  have hg : ∀ᵐ q ∂ρ, ∀ n k : ℕ,
      (fun ω => process D β R hR hJ T (AdaptedContinuous.gridTime n k) (q,ω)) =ᵐ[P]
      HamiltonianJointProcess.process D β R hR T q (AdaptedContinuous.gridTime n k) :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => process_slice D β R hR hJ T _))
  filter_upwards [hg,Measure.ae_ae_of_ae_prod (process_continuous D β R hR hJ T)] with q hg hc
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hg n)),hc,
    HamiltonianJointProcess.process_continuous D β R hR T q] with ω hg hx hy
  intro t
  have he : (fun n => process D β R hR hJ T (AdaptedContinuous.pastGrid t n) (q,ω)) =
      (fun n => HamiltonianJointProcess.process D β R hR T q (AdaptedContinuous.pastGrid t n) ω) :=
    funext (fun n => hg n _)
  have hxlim := (hx.tendsto t).comp (AdaptedContinuous.tendsto_pastGrid t)
  simp only [Function.comp_def] at hxlim
  rw [he] at hxlim
  exact tendsto_nhds_unique hxlim ((hy.tendsto t).comp (AdaptedContinuous.tendsto_pastGrid t))

/-- The genuine all-time canonical parameter solution agrees with the
actual annealed finite-horizon process throughout its physical horizon. -/
theorem process_slice_global (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) :
    ∀ᵐ q ∂ρ, ∀ᵐ ω ∂P, ∀ t, t ≤ T → process D β R hR hJ T t (q,ω) =
      HamiltonianJointProcess.globalProcess D β R hR q t ω := by
  filter_upwards [process_slice_allTimes D β R hR hJ T] with q hq
  have hglobal := GlobalSDE.process_eq_horizon D
    (drift_family_lipschitz β R hR (‖q.1‖₊+1) (⟨q.1,by simp⟩))
    (noise_family_lipschitz N R hR) q.2 T
  filter_upwards [hq,hglobal] with ω hq hglobal
  intro t ht
  exact (hq t).trans (hglobal t ht).symm

end SphericalAging.AnnealedCutoffProcess
