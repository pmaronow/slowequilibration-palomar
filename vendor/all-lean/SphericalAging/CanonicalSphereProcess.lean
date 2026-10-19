module

public import SphericalAging.HamiltonianJointProcess
public import SphericalAging.CutoffSphere

public section

/-! Sphere preservation for the actual canonical parameterized Picard
process on the explicitly constructed null augmentation. The all-path
version is obtained in the same filtration, the genuine SDE equation is
preserved by equality of actual coefficient classes, and radial Itô removes
the cutoff. Thus the parameter process used for the annealed construction
has a proved sphere bound rather than an assumed bounded trajectory.
-/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.CanonicalSphereProcess
open HardSphereDynamics LocalSDE HamiltonianPicardDependence
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1800000

/-- The actual canonical cutoff solution preserves the sphere for every
deterministic disorder and sphere initial state, simultaneously at all
nonnegative times. -/
theorem globalProcess_onSphere (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (q : FiniteModel.Disorder N p × State N) (hq : OnSphere q.2) :
    ∀ᵐ ω ∂P, ∀ t, OnSphere
      (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D) β R hR q t ω) := by
  let D' := NullAugmentation.driver D
  let hb := drift_family_lipschitz β R hR (‖q.1‖₊+1) (⟨q.1,by simp⟩)
  let hsigma := noise_family_lipschitz N R hR
  let X := GlobalSDE.process D' hb hsigma q.2
  have hXa := GlobalSDE.process_stronglyAdapted D' hb hsigma q.2
  have hXc := GlobalSDE.process_continuous D' hb hsigma q.2
  obtain ⟨Y,hYa,hYc,hYX⟩ := NullAugmentation.exists_allPath_continuous_modification_augmented F X hXa hXc
  have hYsol (T : ℝ≥0) : IsLocalStrongSolutionOn (CutoffSDE.cutoffDrift β q.1 R hR)
      (CutoffSDE.cutoffNoise N R hR) (fun i j => (hsigma i j).continuous) D' q.2 Y T :=
    AllPathSDE.IsLocalStrongSolutionOn.path_congr
      (GlobalSDE.process_strongSolution D' hb hsigma q.2 T) hYa (.of_forall hYc) hYX
  have hYsphere : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t, t ≤ GlobalSDE.integerHorizon n → OnSphere (Y t ω) :=
    ae_all_iff.mpr (fun n =>
      (CutoffSphere.physical_solution_of_cutoff hN D' β q.1 R hR hNR q.2 hq Y hYc
        (GlobalSDE.integerHorizon n) (fun i j => (hsigma i j).continuous)
        (hYsol (GlobalSDE.integerHorizon n))).2)
  filter_upwards [hYsphere,hYX] with ω hY hYX
  intro t
  change OnSphere (X t ω)
  rw [← hYX t]
  exact hY (Nat.ceil t) t (GlobalSDE.le_integerHorizon_ceil t)

/-- The canonical process's norm has the manuscript's exact fixed value. -/
theorem globalProcess_norm (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (q : FiniteModel.Disorder N p × State N) (hq : OnSphere q.2) :
    ∀ᵐ ω ∂P, ∀ t, ‖HamiltonianJointProcess.globalProcess (NullAugmentation.driver D) β R hR q t ω‖
      = Real.sqrt N := by
  filter_upwards [globalProcess_onSphere hN D β R hR hNR q hq] with ω hω
  intro t
  rw [← Real.sqrt_sq (norm_nonneg _), (onSphere_iff_norm_sq _).mp (hω t)]

end SphericalAging.CanonicalSphereProcess
